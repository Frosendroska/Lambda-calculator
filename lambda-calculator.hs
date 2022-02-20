import Data.List
import Data.Maybe

type Symb = String 

infixl 2 :@

infix 1 `alphaEq`

infix 1 `betaEq`

data Expr
  = Var Symb
  | Expr :@ Expr
  | Lam Symb Expr
  deriving (Eq, Read, Show)

------------------------ 1 ------------------------
-- возвращающая список свободных переменных терма.
freeVars :: Expr -> [Symb]
freeVars (Var x) = [x]
freeVars (m :@ n) = freeVars m `union` freeVars n
freeVars (Lam x m) = delete x (freeVars m)

-- переименование связанных переменных
renameVar :: String -> Expr -> Expr -> Symb
renameVar x m n
  | x `notElem` freeVars n && x `notElem` freeVars m = x
  | otherwise = renameVar (x ++ "'") n m

-- подстановки терма n вместо всех свободных вхождений переменной v в терме m
subst :: Symb -> Expr -> Expr -> Expr
subst v n (m :@ n') = subst v n m :@ subst v n n'
subst v n (Var x)
  | v == x = n
  | otherwise = Var x
subst v n (Lam x m)
  | v == x = Lam x m
  | x `elem` freeVars n = Lam (renameVar x n m) (subst v n (subst x (Var $ renameVar x n m) m))
  | otherwise = Lam x (subst v n m)

------------------------ 2 ------------------------
-- проверка a-эквивалентности двух термов
alphaEq :: Expr -> Expr -> Bool
alphaEq (m :@ n) (m' :@ n')
  | alphaEq m m' && alphaEq n n' = True
  | otherwise = False
alphaEq (Lam x m) (Lam y n)
  | alphaEq (subst x (Var $ renameVar x m n) m) (subst y (Var $ renameVar x m n) n) = True
  | otherwise = False
alphaEq (Var x) (Var y) = x == y
alphaEq x y = False

------------------------ 3 ------------------------
-- оддношаговая b-редукция, сокращающая левый внешний редекс в терме, если можно
reduceOnce :: Expr -> Maybe Expr
reduceOnce (Var x) = Nothing
reduceOnce ((Lam x m) :@ n) = Just (subst x n m)
reduceOnce (Lam x m) = fmap (Lam x) (reduceOnce m)
reduceOnce (m :@ n) = case reduceOnce m of
  Just y -> Just (y :@ n)
  Nothing -> fmap (m :@) (reduceOnce n)

------------------------ 4 ------------------------
-- многошаговая b-редукция
nf :: Expr -> Expr
nf x = if isNothing (reduceOnce x) then x else nf (fromJust $ reduceOnce x)

------------------------ 5 ------------------------
-- проверка b-эквивалентности двух термов
betaEq :: Expr -> Expr -> Bool
betaEq m n = alphaEq (nf m) (nf n)