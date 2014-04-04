module IST where 

import Data.List
import Data.Char
import System.IO

data Det = Every | All | Some | No | Most
  deriving Show

domain = [1..100]

intDET :: Det -> (Int -> Bool) -> (Int -> Bool) -> Bool
intDET All =  \ p q -> 
  filter (\x -> p x && not (q x)) domain == []

intDET Most = \ p q -> 
 let 
   xs = filter (\x -> p x && not (q x)) domain
   ys = filter (\x -> p x && q x) domain
 in length ys > length xs 

type Name = String
data Id  = Id Name Int deriving (Eq,Ord) 

ix = Id "x" 0
iy = Id "y" 0
iz = Id "z" 0

data Term = Var Id | Struct Name [Term] deriving (Eq,Ord)

x    = Var ix 
y    = Var iy 
z    = Var iz 

zero :: Term 
zero  = Struct "zero" []

s     = Struct "s" 
t     = Struct "t"
u     = Struct "u"

one   = s[zero]
two   = s[one]
three = s[two]
four  = s[three]
five  = s[four]

isVar :: Term -> Bool
isVar (Var _) = True
isVar _       = False

isGround :: Term -> Bool
isGround (Var _) = False
isGround (Struct _ ts) = and (map isGround ts)

varsInTerm :: Term -> [Id]
varsInTerm (Var i)       = [i]
varsInTerm (Struct _ ts) = varsInTerms ts

varsInTerms :: [Term] -> [Id]
varsInTerms = nub . concat . map varsInTerm

data Formula = Atom Name [Term]
             | Eq Term Term
             | Not Formula 
             | Cnj [Formula]
             | Dsj [Formula]
             | Q Det Id Formula Formula
             deriving Show

lfDET :: Det -> 
         (Term -> Formula) -> (Term -> Formula) -> Formula
lfDET All p q  = Q All i (p (Var i)) (q (Var i)) where 
   i = Id "x" (fresh [p zero, q zero])
lfDET Most p q = Q Most i (p (Var i)) (q (Var i)) where 
   i = Id "x" (fresh [p zero, q zero])
lfDET Some p q = Q Some i (p (Var i)) (q (Var i)) where 
   i = Id "x" (fresh [p zero, q zero])
lfDET No p q = Q No i (p (Var i)) (q (Var i)) where 
   i = Id "x" (fresh [p zero, q zero])

type Interp a  = Name -> [a] -> Bool
type FInterp a = Name -> [a] -> a

naturals :: [Integer]
naturals = [0..]

numbers :: [Int]
numbers = [minBound..maxBound]

tVal :: FInterp a -> (Id -> a) -> Term -> a
tVal fint g (Var v)         = g v
tVal fint g (Struct str ts) = 
           fint str (map (tVal fint g) ts)

change :: (Id -> a) -> Id -> a -> Id -> a 
change g v d = \ x -> if x == v then d else g x

qRel :: Eq a => Det -> [a] -> [a] -> Bool
qRel All xs ys = all (\x -> elem x ys) xs 
qRel Some xs ys = any (\x -> elem x ys) xs 
qRel No xs ys = not (qRel Some xs ys) 
qRel Most xs ys = 
  length (intersect xs ys) > length (xs \\ ys)

eval :: Eq a   => 
    [a]        -> 
    Interp a   -> 
    FInterp a  -> 
    (Id -> a)  -> 
    Formula    -> Bool

eval domain i fint = eval' where 
  eval' g (Atom str ts)  = i str (map (tVal fint g) ts)
  eval' g (Eq   t1 t2)   = tVal fint g t1 == tVal fint g t2
  eval' g (Not  f)       = not (eval' g f)
  eval' g (Cnj fs)       = and (map (eval' g) fs)
  eval' g (Dsj fs)        = or  (map (eval' g) fs)
  eval' g (Q det v f1 f2)  = let 
     restr = [ d | d <- domain, eval' (change g v d) f1 ]
     body  = [ d | d <- domain, eval' (change g v d) f2 ]
   in qRel det restr body

form0 = Q Some ix (Atom "Number" [x]) (Atom "Even" [x])

int0 :: Interp Integer
int0 "Number" = \[x] -> True
int0 "Even"   = \[x] -> even x
int0 "Less_than" = \[x,y] -> x < y 

fint0 :: FInterp Integer
fint0 "zero"  []    = 0
fint0 "s"     [i]   = succ i
fint0 "plus"  [i,j] = i + j 
fint0 "times" [i,j] = i * j 

form1 = Q All ix (Atom "Number" [x]) 
          (Q Some iy (Atom "Number" [y]) 
                     (Atom "Less_than" [x,y]))

divides :: Term -> Term -> Formula
divides m n = Q Some iz (Atom "Number" [z]) 
              (Eq n (Struct "times" [m,z]))

data Entity = A | B | C | D | E | F | G
            | H | I | J | K | L | M 
     deriving (Eq,Show,Bounded,Enum)

entities :: [Entity]
entities =  [minBound..maxBound] 

alice, bob, carol :: Entity
alice      = A
bob        = B
carol      = C 

type Pred a = [a] -> Bool

girl, boy :: Pred Entity
girl = \ [x] -> elem x [A,C,D,G]
boy  = \ [x] -> elem x [B,E,F]

love, hate :: Pred Entity
love = \ [x,y] -> elem (x,y) [(A,A),(A,B),(B,A),(C,B)]
hate = \ [x,y] -> elem (x,y) [(B,C),(C,D)]

give, introduce :: Pred Entity
give = \ [x,y,z] -> elem (x,y,z) [(A,H,B),(A,M,E)]
introduce = \ [x,y,z] -> elem (x,y,z) [(A,A,B),(A,B,C)]

passivize :: [a] -> Pred a -> Pred a 
passivize domain r = \ [x] -> any (\ y -> r [y,x]) domain

passivize' :: [a] -> Pred a -> Pred a 
passivize' domain r = \ xs -> any (\ y -> r (y:xs)) domain

self ::  Pred a -> Pred a 
self r = \ (x:xs) -> r (x:x:xs)

self' ::  Pred a -> Pred a 
self' r = \ (x:y:xs) -> r (x:y:x:xs)

swap12 :: Pred a -> Pred a
swap12 r = \ (x:y:xs) -> r (y:x:xs)

data Lit = Pos Name | Neg Name deriving Eq

instance Show Lit where 
  show (Pos x) = x
  show (Neg x) = '-':x

neg :: Lit -> Lit 
neg (Pos x) = Neg x
neg (Neg x) = Pos x

type Clause = [Lit]

names :: [Clause] -> [Name]
names = sort . nub . map nm . concat
  where nm (Pos x) = x
        nm (Neg x) = x

unitProp :: Lit -> [Clause] -> [Clause]
unitProp x cs = concat (map (unitP x) cs)

unitP :: Lit -> Clause -> [Clause]
unitP x ys = if elem x ys then []
              else 
               if elem (neg x) ys 
                then [delete (neg x) ys]
                else [ys]

unit :: Clause -> Bool
unit [x] = True 
unit  _  = False

propagate :: [Clause] -> Maybe ([Lit],[Clause])

propagate cls = 
  prop [] (concat (filter unit cls)) (filter (not.unit) cls) 
  where
    prop :: [Lit] -> [Lit] -> [Clause] 
            -> Maybe ([Lit],[Clause])
    prop xs [] clauses = Just (xs,clauses)
    prop xs (y:ys) clauses = 
      if elem (neg y) xs
       then Nothing
       else prop (y:xs)(ys++newlits) clauses' where 
        newclauses = unitProp y clauses
        zs         = filter unit newclauses
        clauses'   = newclauses \\ zs
        newlits    = concat zs

type KB = ([Clause],[[Clause]])

type Class = Lit

universe :: KB -> [Class]
universe (xs,yss) = 
  map (\ x -> Pos x) zs ++ map (\ x -> Neg x) zs
    where zs = names (xs ++ concat yss)

data Statement = 
     All1  Class   Class | No1     Class Class 
   | Some1 Class   Class | SomeNot Class Class 
   | AreAll Class Class  | AreNo   Class Class 
   | AreAny Class Class  | AnyNot  Class Class
   | What   Class 
  deriving Eq

instance Show Statement where 
  show (All1 as bs)     = 
    "All "  ++ show as ++ " are " ++ show bs ++ "."
  show (No1 as bs)      = 
    "No "   ++ show as ++ " are " ++ show bs ++ "."
  show (Some1 as bs)    = 
    "Some " ++ show as ++ " are " ++ show bs ++ "."
  show (SomeNot as bs) = 
    "Some " ++ show as ++ " are not " ++ show bs ++ "."
  show (AreAll as bs)  = 
    "Are all " ++ show as ++ show bs ++ "?"
  show (AreNo as bs)   = 
    "Are no "  ++ show as ++ show bs ++ "?"
  show (AreAny as bs)  = 
    "Are any " ++ show as ++ show bs ++ "?"
  show (AnyNot as bs)  = 
    "Are any " ++ show as ++ " not " ++ show bs ++ "?"
  show (What as)       = "What about " ++ show as ++ "?"

isQuery :: Statement -> Bool
isQuery (AreAll _ _)  = True
isQuery (AreNo _ _)   = True
isQuery (AreAny _ _)  = True
isQuery (AnyNot _ _)  = True
isQuery (What _)      = True
isQuery  _            = False

negat :: Statement -> Statement
negat (AreAll as bs) = AnyNot as bs
negat (AreNo  as bs) = AreAny as bs
negat (AreAny as bs) = AreNo  as bs
negat (AnyNot as bs) = AreAll as bs

subsetRel :: KB -> [(Class,Class)]
subsetRel kb = 
  [(x,y) | x <- classes, y <- classes, 
     propagate ([x]:[neg y]: fst kb) == Nothing ]
    where classes = universe kb

rSection :: Eq a => a -> [(a,a)] -> [a] 
rSection x r = [ y | (z,y) <- r, x == z ]

supersets :: Class -> KB -> [Class]
supersets cl kb = rSection cl (subsetRel kb)

intersectRel :: KB -> [(Class,Class)]
intersectRel kb@(xs,yys) = 
 nub [(x,y) | x <- classes, y <- classes, lits <- litsList, 
    elem x lits && elem y lits   ]
     where 
       classes = universe kb
       litsList = 
         [ maybe [] fst (propagate (ys++xs)) | ys <- yys ]   

intersectionsets :: Class -> KB -> [Class]
intersectionsets cl kb = rSection cl (intersectRel kb)

derive :: KB -> Statement -> Bool
derive kb (AreAll as bs) = bs `elem` (supersets as kb)
derive kb (AreNo as bs)  = (neg bs) `elem` (supersets as kb)
derive kb (AreAny as bs) = bs `elem` (intersectionsets as kb) 
derive kb (AnyNot as bs) = (neg bs) `elem` 
                               (intersectionsets as kb) 

update  :: Statement -> KB -> Maybe (KB,Bool)

update (All1 as bs) kb@(xs,yss) 
  | bs' `elem` (intersectionsets as kb) = Nothing
  | bs `elem` (supersets  as kb) = Just (kb,False) 
  | otherwise = Just (([as',bs]:xs,yss),True)
 where 
   as' = neg as
   bs' = neg bs

update (No1 as bs) kb@(xs,yss)
  | bs `elem` (intersectionsets as kb) = Nothing
  | bs' `elem` (supersets  as kb) = Just (kb,False)
  | otherwise = Just (([as',bs']:xs,yss),True)
 where    
   as' = neg as 
   bs' = neg bs

update (Some1 as bs) kb@(xs,yss)  
  | bs' `elem` (supersets  as kb) = Nothing
  | bs `elem` (intersectionsets as kb) = Just (kb,False)
  | otherwise = Just ((xs,[[as],[bs]]:yss),True)
 where    
   bs' = neg bs

update (SomeNot as bs) kb@(xs,yss) 
  | bs `elem` (supersets  as kb) = Nothing
  | bs' `elem` (intersectionsets as kb) = Just (kb,False)
  | otherwise = Just ((xs,[[as],[bs']]:yss),True)
 where 
   bs' = neg bs

makeKB :: [Statement] -> Maybe KB
makeKB = makeKB' ([],[]) 
     where 
         makeKB' kb []     = Just kb
         makeKB' kb (s:ss) = case update s kb of 
              Just (kb',_) -> makeKB' kb' ss
              Nothing      -> Nothing

preprocess :: String -> [String]
preprocess = words . (map toLower) .
             (takeWhile (\ x -> isAlpha x || isSpace x))

parse :: String -> Maybe Statement
parse = parse' . preprocess
  where
    parse' ["all",as,"are",bs] = 
      Just (All1 (Pos as) (Pos bs))
    parse' ["no",as,"are",bs] = 
      Just (No1 (Pos as) (Pos bs)) 
    parse' ["some",as,"are",bs] = 
      Just (Some1 (Pos as) (Pos bs)) 
    parse' ["some",as,"are","not",bs] = 
      Just (SomeNot (Pos as) (Pos bs))
    parse' ["are","all",as,bs] = 
      Just (AreAll (Pos as) (Pos bs))
    parse' ["are","no",as,bs] = 
      Just (AreNo (Pos as) (Pos bs)) 
    parse' ["are","any",as,bs] = 
      Just (AreAny (Pos as) (Pos bs)) 
    parse' ["are","any",as,"not",bs] = 
      Just (AnyNot (Pos as) (Pos bs))
    parse' ["what", "about", as] = Just (What (Pos as))
    parse' ["how", "about", as]  = Just (What (Pos as))
    parse' _ = Nothing

process :: String -> KB
process txt = maybe ([],[]) id (mapM parse (lines txt) >>= makeKB)

mytxt = "all bears are mammals\n"
     ++ "no owls are mammals\n"
     ++ "some bears are stupids\n"
     ++ "all men are humans\n"
     ++ "no men are women\n"
     ++ "all women are humans\n"
     ++ "all humans are mammals\n"
     ++ "some men are stupids\n"
     ++ "some men are not stupids"

getKB :: FilePath -> IO KB
getKB p = do 
           txt <- readFile p 
           return (process txt)

u2s :: Clause -> Statement
u2s [Neg x, Pos y] = All1 (Pos x) (Pos y)
u2s [Neg x, Neg y] = No1 (Pos x) (Pos y)

e2s :: [Clause] -> Statement
e2s [[Pos x],[Pos y]] = Some1 (Pos x) (Pos y)
e2s [[Pos x],[Neg y]] = SomeNot (Pos x) (Pos y)

writeKB :: FilePath -> KB -> IO ()
writeKB p (xs,yss) = writeFile p (unlines (univ ++ exist))
  where 
    univ  = map (show.u2s) xs
    exist = map (show.e2s) yss

tellAbout :: KB -> Class -> [Statement]
tellAbout kb as = 
  [All1 as (Pos bs) | (Pos bs) <- supersets as kb, 
                        as /= (Pos bs) ] 
  ++ 
  [No1  as (Pos bs) | (Neg bs) <- supersets as kb, 
                        as /= (Neg bs) ] 
  ++
  [Some1 as (Pos bs) | (Pos bs) <- intersectionsets as kb, 
                      as /= (Pos bs), 
                      notElem (as,Pos bs) (subsetRel kb) ]
  ++
  [SomeNot as (Pos bs) | (Neg bs) <- intersectionsets as kb,  
                   notElem (as, Neg bs) (subsetRel kb) ]

chat :: IO ()
chat = do
 kb <- getKB "kb.txt"
 writeKB "kb.bak" kb
 putStrLn "Update or query the KB:"
 str <- getLine
 if str == "" then return ()
  else do
   handleCases kb str
   chat

handleCases :: KB -> String -> IO ()
handleCases kb str = 
   case parse str of 
     Nothing        -> putStrLn "Wrong input.\n"
     Just (What as) -> let 
         info = (tellAbout kb as, tellAbout kb (neg as)) in 
       case info of 
        ([],[])      -> putStrLn "No info.\n"
        ([],negi)    -> putStrLn (unlines (map show negi))
        (posi,negi)  -> putStrLn (unlines (map show posi))
     Just stmt      -> 
      if isQuery stmt then 
        if derive kb stmt then putStrLn "Yes.\n"
          else if derive kb (negat stmt) 
                 then putStrLn "No.\n" 
                 else putStrLn "I don't know.\n"
        else case update stmt kb of 
          Just (kb',True) -> do 
                              writeKB "kb.txt" kb'
                              putStrLn "OK.\n" 
          Just (_,False)  -> putStrLn 
                              "I knew that already.\n"
          Nothing         -> putStrLn 
                              "Inconsistent with my info.\n"

data S = S NP VP deriving Show
data NP = NP1 NAME | NP2 Det N | NP3 Det RN 
  deriving Show
data ADJ = Beautiful | Happy | Evil 
  deriving Show
data NAME = Alice | Bob | Carol 
  deriving Show
data N = Boy | Girl | Toy | N ADJ N
  deriving Show
data RN = RN1 N That VP | RN2 N That NP TV 
  deriving Show
data That = That deriving Show
data VP = VP1 IV | VP2 TV NP | VP3 DV NP NP deriving Show
data IV = Cheered | Laughed deriving Show
data TV = Admired | Loved | Hated | Helped deriving Show
data DV = Gave | Introduced deriving Show

lfS :: S -> Formula
lfS (S np vp) = (lfNP np) (lfVP vp)

lfNP :: NP -> (Term -> Formula) -> Formula
lfNP (NP1 Alice)   = \ p -> p (Struct "Alice" [])
lfNP (NP1 Bob)     = \ p -> p (Struct "Bob"   [])
lfNP (NP1 Carol)   = \ p -> p (Struct "Carol" [])
lfNP (NP2 det cn)  = (lfDET det) (lfN cn) 
lfNP (NP3 det rcn) = (lfDET det) (lfRN rcn) 

lfVP :: VP -> Term -> Formula
lfVP (VP1 Laughed)   = \ t -> Atom "laugh"   [t]
lfVP (VP1 Cheered)   = \ t -> Atom "cheer"   [t]

lfVP (VP2 tv np) =
    \ subj -> lfNP np (\ obj -> lfTV tv (subj,obj))
lfVP (VP3 dv np1 np2) = 
    \ subj -> lfNP np1 (\ iobj -> lfNP np2 (\ dobj -> 
                          lfDV dv (subj,iobj,dobj)))

lfTV :: TV -> (Term,Term) -> Formula
lfTV Admired  = \ (t1,t2) -> Atom "admire" [t1,t2]
lfTV Hated    = \ (t1,t2) -> Atom "hate" [t1,t2]
lfTV Helped   = \ (t1,t2) -> Atom "help" [t1,t2]
lfTV Loved    = \ (t1,t2) -> Atom "love" [t1,t2]

lfDV :: DV -> (Term,Term,Term) -> Formula
lfDV Gave = \ (t1,t2,t3) -> Atom "give" [t1,t2,t3]
lfDV Introduced = \ (t1,t2,t3) -> 
                    Atom "introduce" [t1,t2,t3]

lfN :: N -> Term -> Formula
lfN Girl     = \ t -> Atom "girl"     [t]
lfN Boy      = \ t -> Atom "boy"      [t]

lfRN :: RN -> Term -> Formula
lfRN (RN1 cn _ vp)    = \ t -> Cnj [lfN cn t, lfVP vp t]
lfRN (RN2 cn _ np tv) = \ t -> Cnj [lfN cn t, 
                       lfNP np (\ subj -> lfTV tv (subj,t))]

lf1 = lfS (S (NP2 Some Boy) 
                   (VP2 Loved (NP2 Some Girl))) 
lf2 = lfS (S (NP3 No (RN2 Girl That (NP1 Bob) Loved)) 
                   (VP1 Laughed))
lf3 = lfS (S (NP3 Some (RN1 Girl That (VP2 Helped (NP1 Alice)))) 
                   (VP1 Cheered))

data W = W Int deriving (Eq,Show) 

rigid :: Entity -> W -> Entity 
rigid x = \ _ -> x

princess :: W -> Pred Entity 
princess = \ w [x] -> case w of 
             W 1 -> elem x [A,C,D,G]
             W 2 -> elem x [A,M]
             _   -> False

type Erel a = [[a]]

bl :: Eq a => Erel a -> a -> [a]
bl r x = head (filter (elem x) r)

restrict :: Eq a => [a] -> Erel a -> Erel a 
restrict domain =  nub . filter (/= []) 
                   . map (filter (flip elem domain)) 

data Agent = Ag Int deriving (Eq,Ord)

a,b,c,d,e :: Agent
a = Ag 0; b = Ag 1; c = Ag 2; d = Ag 3; e = Ag 4

instance Show Agent where
  show (Ag 0) = "a"; show (Ag 1) = "b"; 
  show (Ag 2) = "c"; show (Ag 3) = "d" ; 
  show (Ag 4) = "e";  
  show (Ag n) = 'a': show n 

data EpistM state = Mo
             [state]
             [Agent]
             [(Agent,Erel state)]
             [state]  deriving (Eq,Show)

example :: EpistM Int
example = Mo 
 [0..3]
 [a,b,c]
 [(a,[[0],[1],[2],[3]]),(b,[[0],[1],[2],[3]]),(c,[[0..3]])]
 [1]

rel :: Agent -> EpistM a -> Erel a
rel ag (Mo _ _ rels _) = myLookup ag rels

myLookup :: Eq a => a -> [(a,b)] -> b
myLookup x table = 
   maybe (error "item not found") id (lookup x table)

data Form a = Top 
            | Info a
            | Ng (Form a)
            | Conj [Form a]
            | Disj [Form a]
            | Kn Agent (Form a)
          deriving (Eq,Ord,Show)

impl :: Form a -> Form a -> Form a
impl form1 form2 = Disj [Ng form1, form2]

isTrueAt :: Ord state => 
            EpistM state -> state -> Form state -> Bool
isTrueAt m w Top = True 
isTrueAt m w (Info x) = w == x
isTrueAt m w (Ng f) = not (isTrueAt m w f)
isTrueAt m w (Conj fs) = and (map (isTrueAt m w) fs)
isTrueAt m w (Disj fs) = or  (map (isTrueAt m w) fs)
isTrueAt
 m@(Mo worlds agents acc points) w (Kn ag f) = let 
    r = rel ag m 
    b = bl r w 
  in 
    and (map (flip (isTrueAt m) f) b) 

upd_pa :: Ord state => 
          EpistM state -> Form state -> EpistM state
upd_pa m@(Mo states agents rels actual) f = 
  (Mo states' agents rels' actual') 
   where 
   states' = [ s | s <- states, isTrueAt m s f ]
   rels'   = [(ag,restrict states' r) | (ag,r) <- rels ]
   actual' = [ s | s <- actual, s `elem` states' ]

upds_pa ::  Ord state => 
            EpistM state -> [Form state] -> EpistM state
upds_pa m [] = m 
upds_pa m (f:fs) = upds_pa (upd_pa m f) fs

pairs :: [(Int,Int)]
pairs  = [ (x,y) |  x <- [2..100], y <- [2..100], 
                    x < y, x+y <= 100 ]

msnp :: EpistM (Int,Int)
msnp = (Mo pairs [a,b] acc pairs)
  where 
  acc   = [ (a, [ [ (x1,y1) | (x1,y1) <- pairs,  
                               x1+y1 == x2+y2 ] |
                                 (x2,y2) <- pairs ] ) ]
          ++
          [ (b, [ [ (x1,y1) | (x1,y1) <- pairs,  
                               x1*y1 == x2*y2 ] |
                                 (x2,y2) <- pairs ] ) ]

statement_1 = 
  Conj [ Ng (Kn b (Info p)) | p <- pairs ]

statement_1e = 
  Conj [ Info p `impl` Ng (Kn b (Info p)) | p <- pairs ]

k_a_statement_1e = Kn a statement_1e

statement_2 = 
  Disj [ Kn b (Info p) | p <- pairs ]

statement_2e = 
  Conj [ Info p `impl` Kn b (Info p) | p <- pairs ]

statement_3 = 
  Disj [ Kn a (Info p) | p <- pairs ]

statement_3e =  
  Conj [ Info p `impl` Kn a (Info p) | p <- pairs ]

solution = upds_pa msnp 
           [k_a_statement_1e,statement_2e,statement_3e]

instance Show Id where 
  show (Id name 0) = name 
  show (Id name i) = name ++ show i

instance Show Term where 
  show (Var id)   = show id 
  show (Struct name []) = name 
  show (Struct name ts) = name ++ show ts

fresh :: [Formula] -> Int 
fresh fs = i+1 where i = maximum (0:indices fs)

indices :: [Formula] -> [Int]
indices [] = []
indices (Atom _ _:fs) = indices fs
indices (Eq _ _:fs) = indices fs
indices (Not f:fs)  = indices (f:fs)
indices (Cnj fs1:fs2) = indices (fs1 ++ fs2) 
indices (Dsj fs1:fs2) = indices (fs1 ++ fs2) 
indices (Q _ (Id _ n) f1 f2:fs) = n : indices (f1:f2:fs)

