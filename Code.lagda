\begin{code}
module Code where
\end{code}

definition of natural numbers: Peano Style.

%<*nat>
\begin{code}
data ℕ : Set where
   zero  : ℕ
   suc   : ℕ → ℕ    
\end{code}
%</nat>

Some pragmas to tell Agda to use decimal numbers to represent ℕ values.

\begin{code}
{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}
\end{code}

Addition of natural numbers

%<*plus>
\begin{code}
_+_ : ℕ → ℕ → ℕ
zero   + n = n
suc m  + n = suc (m + n)
\end{code}
%</plus>

Example 1: List concatenation
-----------------------------

Definition of lists.

%<*listdef>
\begin{code}
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A
\end{code} 
%</listdef>

Functions over lists

%<*length>
\begin{code}
length : {A : Set} → List A → ℕ
length []       = 0
length (x ∷ xs) = suc (length xs)
\end{code}
%</length>

%<*concat>
\begin{code}
_++_ : {A : Set} → List A → List A → List A
[] ++ ys       = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
\end{code}
%</concat>

%<*vector>
\begin{code}
data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)
\end{code}
%</vector>

%<*vectorhead>
\begin{code}
head : ∀ {A : Set}{n : ℕ} → Vec A (suc n) → A
head (x ∷ xs) = x
\end{code}
%</vectorhead>

%<*vectorconcat>
\begin{code}
_++v_ : ∀ {n m A} → Vec A n → Vec A m → Vec A (n + m)
[] ++v ys = ys
(x ∷ xs) ++v ys = x ∷ (xs ++v ys) 
\end{code}
%</vectorconcat>

Example 2: List lookup
------------------------

Maybe data type.

%<*maybe>
\begin{code}
data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A
\end{code}
%</maybe>

%<*listhead>
\begin{code}
hd : ∀ {A} → List A → Maybe A
hd []       = nothing
hd (x ∷ xs) = just x 
\end{code}
%</listhead>


Sample lookup without a strong spec.

%<*lookupweak>
\begin{code}
lookupWeak : {A : Set} → ℕ → List A → Maybe A
lookupWeak n       []       = nothing
lookupWeak 0       (x ∷ _)  = just x
lookupWeak (suc n) (_ ∷ xs) = lookupWeak n xs
\end{code}
%</lookupweak>

Boring code for infix operators.

\begin{code}
infix 4 _∈_
infixr 4 _∷_
\end{code}

List membership predicate.

%<*indef>
\begin{code}
data _∈_ {A : Set} : A → List A → Set where
  here  : ∀ {x xs} → x ∈ x ∷ xs
  there : ∀ {x y xs} → y ∈ xs → y ∈ (x ∷ xs)
\end{code}
%</indef>

Function to recover an index from a list membership proof.

%<*index>
\begin{code}
index : ∀ {A : Set}{x : A}{xs : List A} → x ∈ xs → ℕ
index here      = zero
index (there n) = suc (index n)
\end{code}
%</index>

Specification of a lookup algorithm as a data type.

%<*lookupData>
\begin{code}
data Lookup {A}(xs : List A) : ℕ → Set where
  inside  : ∀ x (p : x ∈ xs) → Lookup xs (index p)
  outside : ∀ m → Lookup xs (length xs + m)  
\end{code}
%</lookupData>

Correct by construction list lookup function.

%<*lookupCorrect>
\begin{code}
lookup : {A : Set}(xs : List A)(n : ℕ) → Lookup xs n
lookup [] n = outside n
lookup (x ∷ xs) zero = inside x here
lookup (x ∷ xs) (suc n) with lookup xs n 
lookup (x ∷ xs) (suc .(index p))       | inside y p = inside y (there p)
lookup (x ∷ xs) (suc .(length xs + m)) | outside m = outside m
\end{code}
%</lookupCorrect>

Example 3: type checking lambda terms
---------------------------

Type syntax and contexts

%<*basedefs>
\begin{code}
data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty

Ctx : Set
Ctx = List Ty
\end{code}
%</basedefs>

Expression syntax

%<*rawterms>
\begin{code}
data Exp : Set where
  val : Exp
  var : ℕ → Exp
  abs : Ty → Exp → Exp
  app : Exp → Exp → Exp
\end{code}
%</rawterms>

Type derivations

\begin{code}
infix 4 _⊢_

infixl 4 _,_

_,_ : {A : Set} → List A → A → List A
G , x = x ∷ G
\end{code}

%<*derivation>
\begin{code}
data _⊢_ (G : Ctx) : Ty → Set where
  tval : G ⊢ ι
  tvar : ∀ {t} (p : t ∈ G) → G ⊢ t
  tabs : ∀ t {t'} → G , t ⊢ t' → G ⊢ t ⇒ t' 
  tapp : ∀ {t t'} → G ⊢ (t ⇒ t') → G ⊢ t → G ⊢ t'
\end{code}
%</derivation>

erasure of type derivations

%<*erase>
\begin{code}
erase : ∀ {G t} → G ⊢ t → Exp
erase tval = val
erase (tvar p) = var (index p)
erase (tabs t p) = abs t (erase p)
erase (tapp p p') = app (erase p) (erase p')
\end{code}
%</erase>

Type checker definitions
------------------------

%<*infer>
\begin{code}
data TypeCheck (G : Ctx) : Exp → Set where
  ok : ∀ {t}(d : G ⊢ t) → TypeCheck G (erase d)
  bad : ∀ {e} → TypeCheck G e
\end{code}
%</infer>

%<*typeeq>
\begin{code}
data TyEq : Ty → Ty → Set where
  eq  : ∀ {t} → TyEq t t
  neq : ∀ {t t'} → TyEq t t'
\end{code}
%</typeeq>

%<*typecmp>
\begin{code}
_==_ : (t t' : Ty) → TyEq t t'
ι == ι = eq
ι == (t' ⇒ t'') = neq
(t ⇒ t₁) == ι = neq
(t ⇒ t₁) == (t' ⇒ t'') with t == t' | t₁ == t'' 
(.t' ⇒ .t'') == (t' ⇒ t'') | eq | eq = eq
(t ⇒ t₁) == (t' ⇒ t'') | _ | _ = neq
\end{code}
%</typecmp>

%<*typechecker1>
\begin{code}
tc : ∀ G (e : Exp) → TypeCheck G e
tc G val = ok tval
tc G (var x) with lookup G x 
tc G (var .(index p))      | inside x p = ok (tvar p)
tc G (var .(length G + m)) | outside m = bad
\end{code}
%</typechecker1>
%<*typechecker2>
\begin{code}
tc G (abs t e) with tc (G , t) e 
tc G (abs t .(erase d)) | ok d = ok (tabs t d)
tc G (abs t e)          | bad = bad
\end{code}
%</typechecker2>
%<*typechecker3>
\begin{code}
tc G (app e e') with tc G e | tc G e' 
tc G (app ._ ._ ) | ok {t ⇒ _} d | ok {t'} d₁ with t == t' 
tc G (app ._ ._)  | ok {t ⇒ z} d | ok d₁ | eq = ok (tapp d d₁)
tc G (app ._ ._)  | ok {t ⇒ z} d | ok d₁ | neq = bad
tc G (app e e')   | _       | _ = bad
\end{code}
%</typechecker3>

