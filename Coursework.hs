-------------------------


import Data.List

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
--  deriving Show

instance Show Term where
  show = pretty

example :: Term
example = Lambda "a" (Lambda "x" (Apply (Apply (Lambda "y" (Apply (Variable "a") (Variable "c"))) (Variable "x")) (Variable "b")))

pretty :: Term -> String
pretty = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m 
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m


------------------------- Assignment 1

numeral :: Int -> Term
numeral i = Lambda "f" (Lambda "x" (numeral' i))
  where
    numeral' i
      | i <= 0    = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i-1))


-------------------------

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

------------------------- Assignment 2

variables :: [Var]
variables = map (:[]) ['a'..'z'] ++ [ x : show i | i <- [1..] , x <- ['a'..'z'] ]

filterVariables :: [Var] -> [Var] -> [Var]
filterVariables xs []     = xs 
filterVariables xs (y:ys) = filter (/=y) (filterVariables xs ys)

fresh :: [Var] -> Var
fresh = head . filterVariables variables

used :: Term -> [Var]
used (Variable x) = [x]
used (Lambda x n) = merge [x] (used n)
used (Apply  n m) = merge (used n) (used m)


------------------------- Assignment 3


rename :: Var -> Var -> Term -> Term
rename x y (Variable z)
    | z == x    = Variable y
    | otherwise = Variable z
rename x y (Lambda z n)
    | z == x    = Lambda z n
    | otherwise = Lambda z (rename x y n)
rename x y (Apply n m) = Apply (rename x y n) (rename x y m)


substitute :: Var -> Term -> Term -> Term
substitute x n (Variable y)
    | x == y    = n
    | otherwise = Variable y
substitute x n (Lambda y m)
    | x == y    = Lambda y m
    | otherwise = Lambda z (substitute x n (rename y z m))
    where z = fresh (used n `merge` used m `merge` [x,y])
substitute x n (Apply m p) = Apply (substitute x n m) (substitute x n p)

------------------------- Assignment 4

beta :: Term -> [Term]
beta (Apply (Lambda x n) m) =
  [substitute x m n] ++
  [Apply (Lambda x n') m  | n' <- beta n] ++
  [Apply (Lambda x n)  m' | m' <- beta m]
beta (Apply n m) =
  [Apply n' m  | n' <- beta n] ++
  [Apply n  m' | m' <- beta m]
beta (Lambda x n) = [Lambda x n' | n' <- beta n]
beta (Variable _) = []


normalize :: Term -> Term
normalize n
  | null ns   = n
  | otherwise = normalize (head ns) 
  where ns = beta n

run :: Term -> IO ()
run n = do
  print n
  let ns = beta n
  if null ns then
    return ()
  else
    run (head ns)
    
    
    
--model part A answers copied in for testing purposes
 
-------------------------

suc    = Lambda "n" (Lambda "f" (Lambda "x" (Apply (Variable "f") (Apply (Apply (Variable "n") (Variable "f")) (Variable "x")))))
add    = Lambda "m" (Lambda "n" (Lambda "f" (Lambda "x" (Apply (Apply (Variable "m") (Variable "f")) (Apply (Apply (Variable "n") (Variable "f")) (Variable "x"))))))
mul    = Lambda "m" (Lambda "n" (Lambda "f" (Lambda "x" (Apply (Apply (Variable "m") (Apply (Variable "n") (Variable "f"))) (Variable "x")))))
dec    = Lambda "n" (Lambda "f" (Lambda "x" (Apply (Apply (Apply (Variable "n") (Lambda "g" (Lambda "h" (Apply (Variable "h") (Apply (Variable "g") (Variable "f")))))) (Lambda "u" (Variable "x"))) (Lambda "x" (Variable "x")))))
minus  = Lambda "n" (Lambda "m" (Apply (Apply (Variable "m") dec) (Variable "n")))

-------------------------
-------- PART B --------- 
-------------------------

------------------------- Assignment 5

free :: Term -> [Var] --returning free variables, uses merge from part A, using their definitions
free (Variable x) = [x]
free (Lambda x n) = [a|a<- (free n), a /= x ]
free (Apply  n m) = (free n) `merge` (free m) --merge ensures list is ordered

abstractions :: Term -> [Var] -> Term -- abstracts a term once for each variable in list ith said variable
abstractions n []     = n
abstractions n (x:xs) = Lambda x (abstractions n xs)


applications :: Term -> [Term] -> Term --applies an aplication on a term with a bunch of terms left most first
applications n []    = n
applications n (m:ms)= applications (Apply n m) ms

lift :: Term -> Term --abstracts a term with the variable list and then applies to it all variables from the list
lift n = applications (abstractions n fs) (map Variable fs)
  where fs = (free n)
  


super :: Term -> Term  
super (Variable x) = Variable x --variables end the recursion
super (Apply m n ) = Apply (super m) (super n) 
super (Lambda x n) = lift (Lambda x (aux n)) --when a lambda term is found run aux on the body until it isn't a lamda term
      where aux :: Term -> Term
            aux (Lambda x n) = Lambda x (aux n)
            aux (Apply n m)  = super (Apply n m)
            aux (Variable x) = Variable x



------------------------- Assignment 6

data Expr =
    V Var
  | A Expr Expr

toTerm :: Expr -> Term
toTerm (V x)   = Variable x
toTerm (A m n) = Apply (toTerm m) (toTerm n)

instance Show Expr where
  show = show . toTerm

type Inst = (Var, [Var], Expr)

data Prog = Prog [Inst]


instance Show Prog where
  show (Prog ls) = unlines (map showInst ks)
    where
      ks = map showParts ls
      n  = maximum (map (length . fst) ks)
      showParts (x,xs,e) = (x ++ " " ++ unwords xs , show e)
      showInst (s,t) = take n (s ++ repeat ' ') ++ " = " ++ t


names = ['$':show i | i <- [1..] ]

-------------------------

stripAbs :: Term -> ([Var],Term)
stripAbs (Lambda x n) = ([x] ++ fst(stripAbs n),snd (stripAbs n))--variables in lambda are passed back and and then the term is searched further for more lambdas
stripAbs (Variable x) = ([],Variable x)--applications and variables remain unchanged with no variables passed back
stripAbs (Apply m n ) = ([],Apply m n)

takeAbs :: Term -> [Term]
takeAbs (Lambda x n) = [Lambda x n]--lists all lambda terms so recurs if an application is found
takeAbs (Variable x) = []
takeAbs (Apply m n)  = (takeAbs m) ++ (takeAbs n)

toExpr :: [Var] -> Term -> Expr
toExpr a n = snd (aux a n)
  where
    aux :: [Var] -> Term -> ([Var],Expr)--this aux is neccissary as it passes back the information on the unused fresh variables
    aux (v:vs) (Lambda x m) = (vs,V v)--whenever a lamda is found it is replaced with a variable and the list gets smaller
    aux v (Variable x) = (v,V x)--variables do nothing but changing types from Term to Expr
    aux v (Apply p q ) = (fst b, (A (snd a) (snd b)))--a is first calculated as applying aux to the right hand side, with variables it passes back are then used in b, those unused variables are passed back as fst b and the expression passed back is just the application of a and b
      where
        a = (aux v p)
        b = (aux (fst a) q)
    aux [] (Lambda x m) = ([],V "hello")--this case should never occur unless eroneous data is inputted (not enough variables to replace all the lambdas), "hello" is used as an obvious way to see that this line was called as "hello" is unlikely to be a variable otherwise



toInst :: [Var] -> (Var,Term) -> (Inst,[(Var,Term)],[Var])
toInst v (i,n) = (ins,twolists,v2)
  where (xn, m) = stripAbs n --separating n into abstracted variables and remaining body
        e = (toExpr v m) --replacing abstractions in M with the input list of variables
        ins = (i,xn,e) --this is the instruction triple we return
        abss = (takeAbs m)--finding all the abstractions in M
        v2 = (drop leng v)--this is the fresh names for output
        leng = (length abss)
        
        twolists = (zipWith auxsecond vn abss)--this combines the two lists (of the used variables and the matching abstractions) into 1 list of pairs
        
        vn = (take leng v) -- the number of used variables

        
        auxsecond :: Var -> Term -> (Var, Term)--this function takes a variable and a term and puts them together as a pair
        auxsecond v t = (v,t)




prog :: Term -> Prog
prog n = Prog  (fst (aux names ([("$main",super n)])))--prog starts the program with $main and uses the supercombinator expression of lambda term n to output the corresponding program
  where
    aux :: [Var] -> [(Var,Term)] -> ([Inst], [Var])
    aux x [] = ([],x)
    aux x y 
      |(length y == 1) = ([frst] ++ newfirst,thirdd)--if theres only one instruction we output the instruction part of toInst plus the next instruction to create a list of instructions, it also passes on the remainin fresh names so there will be no duplication
      |otherwise = ([frst] ++ temp1 ++ newfirst,temp2)
        where 
          (frst,secnd,thirdd) = (toInst x (head y))--all purposely spelt wrong to avoid potential clashes with built in functions
          (newfirst,newsecond) = (aux thirdd secnd)
          (temp1,temp2) = (aux thirdd (tail y))--this part is used if there are already multipul insructions






example2 = Apply (Variable "S") (Apply (Apply example (numeral 0)) (Variable "0"))
example3 = Apply (Apply add (numeral 1)) (Apply (Apply mul (numeral 2)) (numeral 3))
example4 = Apply (Apply example3 (Variable "S")) (Variable "0")

------------------------- Assignment 7

sub :: [(Var,Expr)] -> Expr -> Expr
sub []     x = x
sub (e:es) x = (aux e (sub es x))--aux substitutes using a single pair and the expression so this passes on just the head of the pairs and recurs the body until the pairs list is empty
  where
    aux :: (Var,Expr) -> Expr -> Expr
    aux (v,e) (A m n) = (A (aux (v,e) m) (aux (v,e) n)) --if its an application it looks for the variable in the pair in both halves
    aux (v,e) (V x) --once a variable has been found if its in the pair then its substituted for the expression from the pair, if not its left alone
      |(x == v)  = e
      |otherwise = (V x)

step :: [Inst] -> [Expr] -> IO [Expr] --this function runs the first step of the current stack, possibly printing variables and outputting the remaining stack
step i [] = (return [])
step (i:is) ((A m n):xs) = return ([m] ++ [n] ++ xs)
step (i:is) ((V v):xs)
  |(name == "not a normal") = do
  putStr namenew
  putStr " "
  return ([]++xs)
  |((length param) <= (length xs))  = do
  return ([s] ++ (drop (length param)) xs)
  |otherwise      = error "insufficient arguments on stack" --this should only occur with eroneous data. This error message was take from the testing for supernormalize in the coursework instructions
    where
      s = (sub combo ex)--for each step we are either outputting the new stack with head s or printing free variables, where s is the subsitution of the expressions ex by the parameter variables found in findTriple
      V namenew = ex --this is where I stored the name of the variable in the case that it wasn't the name of an instruction, it stores something different if its not used but as its unused it doesn't matter
      combo = (combine param (take (length param) xs))
      (name,param,ex) = (findTriple (i:is) (V v))
      findTriple :: [Inst] -> Expr -> Inst --find tripple takes the list of instructions and the name of an instruction to return the single instruction it refers to
      findTriple [] (V v) = ("not a normal",[],(V v))  --this should occur if and only if the instruction wasn't ion the list this works under the assumption that no normal instruction would be named "not a normal" as they have the form "$i" or "$main"
      findTriple ((name, param, ex):is) (V v)
        |(v == name) = (name, param, ex)
        |otherwise       = (findTriple is (V v))--this looks recursively at each instruction one at a time
      combine :: [Var] -> [Expr] -> [(Var,Expr)]--combine takes 2 lists of same length (one of a variable and one of an expression) and works recursively to return a list of pairs
      combine [] [] = []
      combine (x:xs) (y:ys) = [(x,y)] ++ (combine xs ys)

supernormalize :: Term -> IO ()--this function runs turns a term into a program, runs step with that program with a stack starting with the variable "$main"
supernormalize x = do
    let p = (prog x)
    let init = [V "$main"]
    let aux :: Prog -> [Expr] -> IO [Expr]--this function runs step to completion
        aux p []          = return ([])
        aux (Prog p) init = 
            do x <- (step p init)
               aux (Prog p) x
        
    do aux p init
    return()

      