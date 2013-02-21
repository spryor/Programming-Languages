-- Author: Stephen Pryor
-- Date: Nov. 26, 2012

import Control.Monad.State
import Control.Monad
import Data.List
import Data.Maybe

--------------------------------- Types --------------------------------- START 
type X = String
type Constraint = (Type, Type)
type Substitution = (String, Type)
type Context = [TypeBinding]
type TypeBinding = (String, Type)
--------------------------------- Types --------------------------------- END 

--------------------------------- Data--------------------------------- START 

-- Types--------------------------------- START 
data Type = Fail 
			| TInt 
			| TBool 
			| Fun Type Type 
			| TVar X 
			| TPoly [X] Type deriving Eq
			 
instance Show Type where
	show (Fail) = "Fail"
	show (TInt) = "TInt"
	show (TBool) = "TBool"
	show (Fun t1 t2) =  "(" ++ show (t1) ++ " -> " ++ show (t2) ++ ")" 
	show (TVar x) = x
	show (TPoly x t1) = "(TPoly " ++ show (x) ++ " " ++ show (t1) ++ ")" 
-- Types--------------------------------- END

-- Terms--------------------------------- START 
data Term = Var X 
			| Lam X Term 
			| App Term Term 
			| Let X Term Term 
			| Rec X Term 
			| Num Int 
			| Binary X Term Term

instance Show Term where
	show (Var x) = "("++x++")"
	show (Lam x term) = "(Lam " ++ x ++ ". " ++ show (term) ++ ")"
	show (App t1 t2) = "(" ++ show (t1) ++ " " ++ show (t2) ++ ")"
	show (Let x t1 t2) = "(Let " ++ x ++ " = " ++ show (t1) ++ " in " ++ show (t2) ++ ")"
	show (Rec x term) = "(Rec (" ++ x ++ ") " ++ show (term) ++ ")" 
	show (Num i) = show i
	show (Binary x t1 t2) = "(" ++ show(t1) ++ " " ++ x ++ " " ++ show(t2) ++ ")"
-- Terms--------------------------------- END
	
data InferState = InferState Int [Constraint] deriving Show
--------------------------------- Data --------------------------------- END

--------------------------------- State Monad Functions --------------------------------- START 
initialState = InferState 1 []

incVar :: State InferState ()
incVar = do
		InferState n c <- get
		put (InferState (n+1) c)

newVar :: State InferState Type
newVar = do
		InferState n c <- get
		incVar
		return (TVar ("T" ++ (show n)))
--------------------------------- State Monad Functions --------------------------------- END 

--------------------------------- getConsts Functions --------------------------------- START
getConsts :: Term -> Context -> State InferState Type

getConsts (Var t) context = do
				case lookup t context of
					Just rType -> return rType
					_ -> return Fail                           

getConsts (Lam x t2) context = do
				t1Type <- newVar
				let newContext = (context ++ [(x, t1Type)])
				t2Type <- getConsts t2 newContext
				return (Fun t1Type t2Type)

getConsts (Num i) context = do return TInt

getConsts (App t1 t2) context = do
				t1Type <- getConsts t1 context
				t2Type <- getConsts t2 context
				newTVar <- newVar
				InferState n c <- get
				put (InferState n (c ++ [(t1Type, (Fun t2Type newTVar))]))
				return newTVar

getConsts (Binary op t1 t2) context = do
				newTVar' <- getConsts t1 context
				newTVar'' <- getConsts t2 context
				newTVar <- newVar
				InferState n c <- get
				case op of 
					"+" -> put(InferState n (c ++ [(newTVar', TInt),(newTVar'', TInt),(newTVar, TInt)]))
					"-" -> put(InferState n (c ++ [(newTVar', TInt),(newTVar'', TInt),(newTVar, TInt)]))
					"<" -> put(InferState n (c ++ [(newTVar', TInt),(newTVar'', TInt),(newTVar, TBool)]))
					"&&" -> put(InferState n (c ++ [(newTVar', TBool),(newTVar'', TBool),(newTVar, TBool)]))
					"||" -> put(InferState n (c ++ [(newTVar', TBool),(newTVar'', TBool),(newTVar, TBool)]))
					"=" -> 	put(InferState n (c ++ [(newTVar', newTVar''),(newTVar, TBool)]))
				return newTVar

getConsts (Let x t1 t2) context = do
				t1Type <- getConsts t1 context
				t2Type <- getConsts (substTerm x t1 t2) context
				return t2Type

getConsts (Rec x t1) context = do
				xType <- newVar
				let newContext = (context ++ [(x, xType)])
				newTVar <- getConsts t1 newContext
				InferState n c <- get
				put (InferState n (c ++ [(xType, newTVar)]))
				return newTVar					
--------------------------------- getConsts Functions --------------------------------- END

--------------------------------- unify Functions --------------------------------- START
unify :: [Constraint] -> [Substitution]
unify [] = []
unify ((s, t):xs) | s == t = unify xs
unify ((TVar x, t):xs) | x `notElem` fv (t) = compose (unify (subst (TVar x) t xs)) [(x, t)]
unify ((s, TVar x):xs) | x `notElem` fv (s) = compose (unify (subst (TVar x) s xs)) [(x, s)]
unify ((Fun s1 s2, Fun t1 t2):xs) = unify (xs ++ [(s1, t1)] ++ [(s2, t2)])
unify _ = [("x", Fail)] 
--------------------------------- unify Functions --------------------------------- END

--------------------------------- infer Functions --------------------------------- START
infer :: Term -> Type
infer term = let (result, (InferState _ constraints)) = (runState (getConsts term []) initialState) in
				let substitutions = unify (constraints) in
					if ("x", Fail) `elem` substitutions
					then
						Fail
					else
						let returnType = (typeSubstitution substitutions result) in
							let fvs = fv returnType in 
								case fvs of
									[] -> returnType
									otherwise -> TPoly fvs returnType
--------------------------------- infer Functions --------------------------------- END
			
--------------------------------- DEBUG Functions --------------------------------- START
extractConstraints :: InferState -> [Constraint] 
extractConstraints (InferState num cList) = cList

getConsts' :: Term -> [Constraint]
getConsts' term = extractConstraints (execState (getConsts term []) initialState)

stateInfer :: Term -> (Type, InferState)
stateInfer term = (runState (getConsts term []) initialState)

unifyInfer :: Term -> [Substitution]
unifyInfer term = let (result, (InferState _ constraints)) = (runState (getConsts term []) initialState) in
					let substitutions = unify (constraints) in
						substitutions

cases = [(TInt, (Num 1)),
		(TInt, (Binary "-" (Num 2) (Num 1))),
		(TBool, (Binary "=" (Num 2) (Binary "-" (Num 3) (Num 1)))),
		(Fail, (Binary "=" (Num 2) (Binary "=" (Num 3) (Num 1)))),
		(TInt, (App (Lam "x" (Var "x")) (Num 5))),
		(TPoly ["T1"] (Fun (TVar "T1") (TVar "T1")), (Lam "x" (Var "x"))),
		(Fail, (Rec "g" (Lam "n" (App (Var "g") (Var "g"))))),
		(TPoly ["T2","T3"] (Fun (TVar "T2") (TVar "T3")), (Rec "g" (Lam "n" (App (Var "g") (Var "n"))))),
		(Fun TInt TInt, (Rec "g" (Lam "n" (App (Var "g") (App (Var "g") (Num 5)))))),
		(Fail, (Rec "g" (App (Var "g") (App (Var "g") (Num 5))))),
		(TPoly ["T2"] (Fun (TVar "T2") (TVar "T2")), (Rec "g" (Lam "n" (Var "n")))),
		(TPoly ["T9"] (Fun TInt (Fun (Fun (TVar "T9") (TVar "T9")) (Fun (TVar "T9") (TVar "T9")))), (Rec "apply-n" (Lam "n" (Lam "f" (Lam "x" (App (Var "f") (App (App (App (Var "apply-n") (Binary "-" (Var "n") (Num 1))) (Var "f")) (App (Var "f") (Var "x"))))))))),
		(TBool, (Let "id" (Lam "x" (Var "x")) (App (Var "id") (Binary "=" (Num 1) (Num 2))))),
		(TInt, (Let "id" (Lam "x" (Var "x")) (App (Var "id") (Binary "+" (Num 1) (Num 2))))),
		(TInt, (Let "id" (Lam "x" (Var "x")) (App (Var "id") (Binary "+" (App (Var "id") (Num 1)) (Num 2))))),
		(TBool, (Let "id" (Lam "x" (Var "x")) (App (Var "id") (Binary "=" (App (Var "id") (Num 1)) (Num 2))))),
		(TPoly ["T9"] (Fun TInt (Fun (Fun (TVar "T9") (TVar "T9")) (Fun (TVar "T9") (TVar "T9")))), (Rec "apply-n" (Lam "n" (Lam "f" (Lam "x" (App (Var "f") (App (App (App (Var "apply-n") (Binary "-" (Var "n") (Num 1))) (Var "f")) (App (Var "f") (Var "x"))))))))),
		(Fun TBool TBool, (Let "g" (Rec "apply-n" (Lam "n" (Lam "f" (Lam "x" (App (Var "f") (App (App (App (Var "apply-n") (Binary "-" (Var "n") (Num 1))) (Var "f")) (App (Var "f") (Var "x")))))))) (App (App (Var "g") (Num 5)) (Lam "b" (Binary "=" (Num 1) (Num 1)))))),
		(Fun TBool TBool, (Let "g" (Rec "apply-n" (Lam "n" (Lam "f" (Lam "x" (App (Var "f") (App (App (App (Var "apply-n") (Binary "-" (Var "n") (Num 1))) (Var "f")) (App (Var "f") (Var "x")))))))) (App (App (Var "g") ((App (App (App (Var "g") (Num 2)) (Lam "i" (Binary "+" (Var "i") (Num 1)))) (Num 0)))) (Lam "b" (Binary "=" (Num 1) (Num 1)))))),
		(Fail, (Let "g" (Rec "apply-n" (Lam "n" (Lam "f" (Lam "x" (App (Var "f") (App (App (App (Var "apply-n") (Binary "-" (Var "n") (Num 1))) (Var "f")) (App (Var "f") (Var "x")))))))) (App (App (Var "g") ((App (App (App (Var "g") (Num 2)) (Lam "i" (Binary "=" (Var "i") (Num 1)))) (Num 0)))) (Lam "b" (Binary "=" (Num 1) (Num 1))))))]

--A function to test the type inference on 
--a list of cases 
--Usage: runTestCases cases
runTestCases :: [(Type, Term)] -> String
runTestCases [] = "All are correct!!"
runTestCases ((result, term):cases) | (infer term == result) = runTestCases cases
						     	 	 | otherwise = "Error: infer " ++ show term	
	
--------------------------------- DEBUG Functions --------------------------------- END

{-%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% -- HELPER FUNCTIONS -- %%%%%%%%%%%%%%%%%%%%%% - START -}

--------------------------------- fv Functions --------------------------------- START
fv :: Type -> [String]
fv (Fun t1 t2) = (fv (t1)) `union` (fv (t2))
fv (TVar x) = [x]
fv _ = []
--------------------------------- fv Functions --------------------------------- END


--------------------------------- typeSubstitution Functions --------------------------------- START
typeSubstitution :: [Substitution] -> Type -> Type
typeSubstitution subs TInt = TInt
typeSubstitution subs TBool = TBool
typeSubstitution subs (Fun t1 t2) = Fun (typeSubstitution subs t1) (typeSubstitution subs t2)
typeSubstitution subs (TVar x) | x `elem` (dom (subs)) = extractMapping subs x
						     | otherwise = (TVar x)
--------------------------------- typeSubstitution Functions --------------------------------- END

--------------------------------- extractMapping Functions --------------------------------- START
extractMapping :: [Substitution] -> String -> Type
extractMapping ((x, t):xs) var | x==var = t
						  | otherwise = extractMapping xs var
--------------------------------- extractMapping Functions --------------------------------- END

--------------------------------- dom Functions --------------------------------- START
dom :: [Substitution] -> [String]
dom [] = []
dom ((x, t):xs) = [x] ++ dom xs
--------------------------------- dom Functions --------------------------------- END

--------------------------------- compose Functions --------------------------------- START
compose :: [Substitution] -> [Substitution] -> [Substitution]
compose sigma gamma = (subSigma sigma gamma) ++ (subGamma sigma gamma)

subSigma :: [Substitution] -> [Substitution] -> [Substitution]
subSigma [] _ = []
subSigma ((x, t):sigma) gamma | x `notElem` (dom (gamma)) = [(x, t)] ++ (subSigma sigma gamma)
						       | otherwise = (subSigma sigma gamma)

subGamma :: [Substitution] -> [Substitution] -> [Substitution]
subGamma _ [] = []
subGamma sigma ((x, t):gamma) = [(x, (typeSubstitution sigma t))] ++ (subGamma sigma gamma)
--------------------------------- compose Functions --------------------------------- END

--------------------------------- subst Functions --------------------------------- START
subst :: Type -> Type -> [Constraint] -> [Constraint]
subst subT newT [] = []
subst subT newT ((s, t):xs) = [(subst_type subT newT s, subst_type subT newT t)] ++ (subst subT newT xs)
--------------------------------- subst Functions --------------------------------- END

--------------------------------- subst_type Functions --------------------------------- START
subst_type :: Type -> Type -> Type -> Type
subst_type subT newT (Fun t1 t2) = Fun (subst_type subT newT t1) (subst_type subT newT t2)
subst_type subT newT (TPoly lst t1) = TPoly lst (subst_type subT newT t1)
subst_type (TVar x) newT (TVar y) | x == y = newT
subst_type subT newT val = val
--------------------------------- subst_type Functions --------------------------------- END


--------------------------------- freeVars --------------------------------- START 
freeVars :: Term -> [String]
freeVars (Var s) = [s]
freeVars (Lam i e) = (freeVars e) \\ [i]
freeVars (App f a) = (freeVars f) `union` (freeVars a)
freeVars (Let x f a) = (freeVars f) `union` (freeVars a) \\ [x]
freeVars (Binary x f a) = (freeVars f) `union` (freeVars a)
freeVars (Rec x t) = [x] `union` (freeVars t)
freeVars (Num num) = []
--------------------------------- freeVars --------------------------------- END 

--------------------------------- fresh --------------------------------- START 
fresh :: [String] -> String
fresh x = incr 0 x
--------------------------------- fresh --------------------------------- END 

--------------------------------- incr --------------------------------- START 
incr :: Int -> [String] -> String
incr num fvars | ("x" ++ (show num)) `elem` fvars = incr (num+1) fvars
			   | otherwise = ("x" ++ (show num))
--------------------------------- incr --------------------------------- END 

--------------------------------- substTerm --------------------------------- START 
substTerm :: String -> Term -> Term -> Term
substTerm x t (Var s) | s == x = t
				 	  | s /= x = Var s
substTerm x t (App t1 t2) = App (substTerm x t t1) (substTerm x t t2)
substTerm x t (Lam y t1) | x == y = Lam y t1
						 | y `elem` (freeVars t) = Lam f (substTerm y (Var f) t1)
				  		 | x /= y = Lam y (substTerm x t t1)
				  		 where f = fresh (freeVars t)
substTerm x t (Let y t1 t2) | y `elem` (freeVars t) = substTerm x t (Let f t11 (substTerm y (Var f) t1))
							| x == y = Let y t11 t2
				  			| x /= y = Let y t11 (substTerm x t t2)
				  			where 
				  				  f = fresh (freeVars t)
				  			 	  t11 = substTerm x t t1
substTerm x t (Num i) = Num i
substTerm x t (Binary op t1 t2) = Binary op (substTerm x t t1) (substTerm x t t2)
substTerm x t (Rec y t1) = Rec y (substTerm x t t1) 
--------------------------------- substTerm --------------------------------- END 

{-%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% -- HELPER FUNCTIONS -- %%%%%%%%%%%%%%%%%%%%%% - END -}


