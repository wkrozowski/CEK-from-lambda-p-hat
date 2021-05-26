module cek where
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_; proj₁; proj₂; _,_; ∃; Σ-syntax; Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym)
open import Data.Sum using (_⊎_; inj₁; inj₂) 
open import Relation.Nullary using (¬_)

id : ∀ {a : Set}
   → a
   → a
   
id x = x

module Terms where
  -- Types are inductively defined set consisting of the base type and function type
  data Type : Set where
    ● : Type
    _⇒_ : Type → Type → Type

  -- Typing contexts are simply lists of types. Note, we don't use any variable identifiers. The reason for that is the fact that we use intrinsically typed De Brujin representations.
  Context : Set
  Context = List Type

  -- Following PLFA we can define a variable lookup operation:
  data _∋_ : Context → Type → Set where
    Z : ∀ {Γ σ}
        → (σ ∷ Γ) ∋ σ

    S : ∀{Γ σ τ}
        → Γ ∋ σ
        → (τ ∷ Γ) ∋ σ

  -- As for the terms, we consider intrinsically typed, DeBrujin Simply Typed Lambda Calculus (see chapter DeBrujin of PLFA)
  data _⊢_ : Context → Type → Set where

    ƛ_ : ∀ {Γ σ τ}
        → (σ ∷ Γ) ⊢ τ
        → Γ ⊢ (σ ⇒ τ)

    _∘_ : ∀ {Γ τ σ }
        → Γ ⊢ (σ ⇒ τ)
        → Γ ⊢ σ
        → Γ ⊢ τ


    `_ : ∀ {Γ σ }
        → Γ ∋ σ
        → Γ ⊢ σ

  -- Following Biernacka and Danvy's version of extended Curien's calculus of closures, introduce data typed representing closed terms, as well as environments.
  -- Note that those aren't typing contexts; environments represent substitutions

  mutual
    data Closed : Type → Set where
      Closure : ∀ { Γ u }
              → Γ ⊢ u
              → Env Γ
              → Closed u

      Clapp : ∀ { u v }
            → Closed (u ⇒ v)
            → Closed u
            → Closed v

    data Env : Context → Set where
      Nil : Env []

      _·_ : ∀ { G u }
          → Closed u
          → Env G
          → Env (u ∷ G)

module Redex where
  open Terms

    -- Helper function for recognising valid closed values in the language,  as we are dealing with STLC, the lambda closure is the only value we have
  isVal : ∀ {σ} → Closed σ → Set
  isVal (Closure (ƛ body) env) =  ⊤
  isVal _ = ⊥

  -- Now define a datatype for values, which includes a closure and witness, that it is indeeed a value
  data Value (σ : Type) : Set where
    Val : (c : Closed σ) → isVal c → Value σ
    
  -- Redexes stand for reducible expressions. Either it is a variable lookup, application of two terms in given enviroment, or beta reduction given closed argument
  data Redex : Type → Set where
    Lookup : ∀ {Γ σ}
           → Γ ∋ σ
           → Env Γ
           → Redex σ

    App : ∀ {Γ σ τ}
           → Γ ⊢ (σ ⇒ τ)
           → Γ ⊢ σ
           → Env Γ
           → Redex τ

    Beta : ∀ {Γ τ σ}
           → (σ ∷ Γ) ⊢ τ
           → Env Γ
           → Value σ
           → Redex τ

    -- We can easily convert a redex to corresponding closure
  fromRedex : ∀ {u}
              → Redex u
              → Closed u
  fromRedex (Lookup x env) = Closure (` x) env
  fromRedex (App f arg env) = Closure (f ∘ arg) env
  fromRedex (Beta body env (Val c _)) = Clapp (Closure (ƛ body) env) c

  -- Define lookup from substitution enviroments
  _!_ : ∀ {Γ u}
      → Env Γ
      → Γ ∋ u
      → Closed u

  Nil ! ()
  (x · _)  ! Z = x
  (x · xs) ! S r = xs ! r

  -- Contract computes the result of closing a single redex, it is a single step redution
  contract : ∀ {u} → Redex u → Closed u
  contract (Lookup i env) = env ! i
  contract (App f x env) = Clapp (Closure f env) (Closure x env)
  contract (Beta body env (Val c x)) = Closure body (c · env)

   -- Evaluation contexts are another name for continuations, known from CEK machine.
  -- We use Swierstra's parametrised notion of continuation.
  -- EvalContext a b means, that if giving Closed term of type a i can produce something of term b while plugging

  data EvalContext : Type → Type → Set where
    -- MT is simply empty frame
    MT : ∀ {u}
         → EvalContext u u

    -- Contary to Swierstra's formalization, we add one more continuation frame, which is present in CEK machine, for evaluating a function.
    -- It allows us to build an applicative order evaluator.
    FN : ∀ {a b c}
         → Value (a ⇒ b)
         → EvalContext b c
         → EvalContext a c

    -- ARG is the same as in Krivine machine - it holds an evaluate argument, while evaluating a function
    ARG : ∀ {u v w}
        → Closed u
        → EvalContext v w
        → EvalContext (u ⇒ v) w

  -- Plug takes an evaluation context and a closed term to produce term of it's output type
  plug : ∀ {u v}
         → EvalContext u v
         → Closed u
         → Closed v

  plug MT f = f
  plug (ARG x ctx) f = plug ctx (Clapp f x)
  plug (FN (Val closed isval) ctx) x = plug ctx (Clapp closed x)

  redexIsNotValue : ∀ {u}
                  → (r : Redex u)
                  → (isVal (fromRedex r) → ⊥)
  redexIsNotValue (Lookup _ _) = id
  redexIsNotValue (App _ _ _ ) = id
  redexIsNotValue (Beta _ _ (Val _ _)) = id

  pluggingNotVal : ∀ {u v}
                 → (ctx : EvalContext u v)
                 → (c : Closed u)
                 → (proof : (isVal c → ⊥))
                 → (isVal (plug ctx c) → ⊥)
  pluggingNotVal MT c proof = proof
  pluggingNotVal (FN (Val (Closure (ƛ body) env) _) ctx) c proof = pluggingNotVal ctx (Clapp (Closure (ƛ body) env) c) id
  pluggingNotVal (ARG x ctx) c proof = pluggingNotVal ctx (Clapp c x) id


  plugLemma : ∀ {u v}
            → (c : EvalContext u v)
            → (r : Redex u)
            → (isVal (plug c (fromRedex r))) → ⊥
  plugLemma c r = pluggingNotVal c (fromRedex r) (redexIsNotValue r)

    -- This strictly follows Swierstra mechanisation of Krivine machine.
  -- He introduced Decomposition data type, which is equivalent to Value + Redex × Context typed
  -- from Biernacka and Danvy's paper, however thanks to the use of dependent types, Redex×Context can continuation
  -- Redex and context which after plugging will create a correct closed expression.
  data Decomposition : ∀ {u} → Closed u → Set where
    Val : ∀ {u v Γ}
        → (body : (u ∷ Γ) ⊢ v)
        → (env : Env Γ)
        → Decomposition (Closure (ƛ body) env)

    Redex×Context : ∀ {v u}
                  → (r : Redex u)
                  → (ctx : EvalContext u v)
                  → Decomposition (plug ctx (fromRedex r))
                  
  --Now we define decomposition function, which takes a closed term in a given context, and peels it off to the form where it can be contracted.
   
  {-# TERMINATING #-}
  mutual
    decompose' : ∀ { u v}
               → (ctx : EvalContext u v)
               → (c : Closed u)
               → Decomposition (plug ctx c)

    decompose' ctx (Closure (` i) env) =
      Redex×Context (Lookup i env) ctx
      
    decompose' ctx (Closure (ƛ body) env) =
      decompose'_aux ctx (body) env
    decompose' ctx (Closure (f ∘ x) env) =
      Redex×Context (App f x env) ctx
    decompose' ctx (Clapp f x) =
      decompose' (ARG x ctx) f

    -- The auxillary function peels of the lambda closure basing on the continuation frame
    decompose'_aux : ∀ { a b w Γ}
                   → (ctx : EvalContext (a ⇒ b) w)
                   → (body : (a ∷ Γ) ⊢  b)
                   → (env : Env Γ)
                   → Decomposition (plug ctx (Closure (ƛ body) env))

    decompose'_aux MT body env = Val body env
    decompose'_aux (ARG arg ctx) body env = decompose' (FN (Val (Closure (ƛ body) env) tt) ctx) arg
    decompose'_aux (FN (Val (Closure (ƛ x) env₂) proof) ctx) body env =
      Redex×Context (Beta x env₂ (Val (Closure (ƛ body) env) tt)) ctx

      -- We decompose starting from empty frame
    decompose : ∀ {u}
              → (c : Closed u)
              → Decomposition c

    decompose c = decompose' MT c

    
     -- Head reduction step consists of unplugging, contraction and plugging
    -- Repeated head reduction eventually leads to a norma form.
    headReduce : ∀ {u}
              → Closed u
              → Closed u

    headReduce c with decompose c
    headReduce .(Closure (ƛ body) env) | Val body env =
      Closure (ƛ body) env
    headReduce .(plug ctx (fromRedex redex)) | Redex×Context redex ctx =
      plug ctx (contract redex)


    -- Danvy's refocusing lemma
    decomposePlug : ∀ {u v}
                  → (ctx : EvalContext u v)
                  →  (c : Closed u)
                  → decompose (plug ctx c) ≡ decompose' ctx c
    decomposePlug MT c = refl
    decomposePlug (FN (Val (Closure (ƛ body) env) _) ctx) c
      rewrite decomposePlug ctx (Clapp ((Closure (ƛ body) env)) c) = refl
    decomposePlug (ARG x ctx) c
      rewrite decomposePlug ctx (Clapp c x) = refl


    decomposeRedex : ∀ {u v}
                   → (ctx : EvalContext u v)
                   → (r : Redex u)
                   → decompose' ctx (fromRedex r) ≡ Redex×Context r ctx
    decomposeRedex MT (Lookup _ _) = refl
    decomposeRedex (FN _ _) (Lookup _ _) = refl
    decomposeRedex (ARG _ _) (Lookup _ _) = refl
    decomposeRedex MT (App _ _ _) = refl
    decomposeRedex (FN _ _) (App _ _ _) = refl
    decomposeRedex (ARG _ _) (App _ _ _) = refl
    decomposeRedex MT (Beta _ _ (Val (Closure (ƛ _) _) _)) = refl
    decomposeRedex (FN _ _) (Beta _ _ (Val (Closure (ƛ _) _) _)) = refl
    decomposeRedex (ARG _ _) (Beta _ _ (Val (Closure (ƛ _) _) _)) = refl

    headReducePlug : ∀ {u v}
                   → (ctx : EvalContext u v)
                   → (r : Redex u)
                   → headReduce (plug ctx (fromRedex r)) ≡ plug ctx (contract r)
    headReducePlug ctx r rewrite decomposePlug ctx (fromRedex r)
                         | decomposeRedex ctx r = refl
  
  -- Reverse view on the continuation frames - snoc sourced from Swierstra
  snoc : ∀ {u v w}
       → EvalContext u (v ⇒ w)
       → (Closed v)
       → EvalContext u w

  snoc MT u = ARG u MT
  snoc (FN x ctx) u = FN x (snoc ctx u)
  snoc (ARG x ctx) u = ARG x (snoc ctx u)

  -- cons is it's call-by-value dual
  cons : ∀ {a b c}
       → EvalContext a b
       → (Value (b ⇒ c))
       → EvalContext a c
  cons MT val = FN val MT
  cons (FN x ctx) val = FN x (cons ctx val)
  cons (ARG x ctx) val = ARG x ((cons ctx val))

  -- Extended reverse view data structure
  data SnocView : {u v : Type} → (ctx : EvalContext u v) → Set where
    Nil : ∀ {u}
        → SnocView {u} {u} MT

    Cons : ∀ {a b c}
          → (val : Value (b ⇒ c))
          → (ctx : EvalContext a b)
          → (SnocView (cons ctx val))
        
    Snoc : ∀ {u v w}
         → (x : Closed v)
         → (ctx : EvalContext u (v ⇒ w))
         → SnocView (snoc ctx x)

  -- propagate last frame
  viewSnoc : ∀ {u v}
           → (ctx : EvalContext u v)
           → SnocView ctx
  viewSnoc MT = Nil
  viewSnoc (FN x ctx) with viewSnoc ctx
  viewSnoc (FN x .MT) | Nil = Cons x MT
  viewSnoc (FN x .(cons ctx val)) | Cons val ctx = Cons val (FN x ctx)
  viewSnoc (FN x .(snoc ctx x₁)) | Snoc x₁ ctx = Snoc x₁ (FN x ctx)
  viewSnoc (ARG x ctx) with viewSnoc ctx
  viewSnoc (ARG x .MT) | Nil = Snoc x MT
  viewSnoc (ARG x .(cons ctx val)) | Cons val ctx = Cons val (ARG x ctx)
  viewSnoc (ARG x .(snoc ctx x₁)) | Snoc x₁ ctx = Snoc x₁ (ARG x ctx)

  -- Snoc is lhs application
  snocClapp : ∀ {u v w}
            → (ctx : EvalContext u (v ⇒ w))
            → (x : Closed v)
            → (t : Closed u)
            → plug (snoc ctx x) t ≡ Clapp (plug ctx t) x
  snocClapp MT x t = refl
  snocClapp (FN (Val fn _) ctx) x t rewrite snocClapp ctx x (Clapp fn t) = refl
  snocClapp (ARG arg ctx) x t rewrite snocClapp ctx x (Clapp t arg) = refl


  -- Cons is rhs application
  consClapp : ∀ {a b c}
            → (ctx : EvalContext a b)
            → (fn : Closed (b ⇒ c))
            → (proof : isVal fn)
            → (t : Closed a ) 
            → plug (cons ctx (Val fn proof) ) t ≡ Clapp fn (plug ctx t)
  consClapp MT fn proof t = refl
  consClapp (FN (Val c proof₁) ctx) fn proof₂ t rewrite consClapp ctx fn proof₂ (Clapp c t) = refl
  consClapp (ARG x ctx) fn proof t rewrite consClapp ctx fn proof (Clapp t x) = refl

-- Properties of Clapp - sourced from Swierstra
  clappL : ∀ {u v}
          → {f f' : Closed (u ⇒ v)}
             {x x' : Closed u}
          → Clapp f x ≡ Clapp f' x'
          → f ≡ f'
  clappL refl = refl

  clappR : ∀ {u v}
          → {f f' : Closed (u ⇒ v)}
             {x x' : Closed u}
          → Clapp f x ≡ Clapp f' x'
          → x ≡ x'
  clappR refl = refl

  clappU : ∀ {u u' v}
         → {f : Closed (u ⇒ v)}
            {f' : Closed (u' ⇒ v)}
            {x : Closed u}
            {x' : Closed u'}
         → Clapp f x ≡ Clapp f' x'
         → u ≡ u'
  clappU refl = refl

  -- Head reduction lemmas
  headReduceLemma : ∀ {u v}
                  → (f : Closed (u ⇒ v))
                  → (x : Closed u)
                  → (fx : Closed v)
                  → (Clapp f x ≡ fx) 
                  → (isVal f → ⊥)
                  → headReduce fx ≡ Clapp (headReduce f) x

  headReduceLemma f x fx eq p with decompose fx
  headReduceLemma f x .(plug ctx (fromRedex r)) eq p
      | Redex×Context r ctx with viewSnoc ctx 
  headReduceLemma f x .(plug MT (fromRedex (Beta {Γ = _} {τ = _} {σ = _} x₁ x₂ (Val c x₃)))) eq p
      | Redex×Context (Beta x₁ x₂ (Val c x₃)) .MT
      | Nil with clappU eq
  ... | refl rewrite (clappL eq) = ⊥-elim (p tt)
  headReduceLemma f x .(plug (cons ctx (Val c x₁)) (fromRedex r)) eq p
      | Redex×Context r .(cons ctx (Val c x₁))
      | Cons (Val c x₁) ctx rewrite consClapp ctx c x₁ ((contract r))
      | consClapp ctx c x₁ (fromRedex r) with clappU eq
  ... | refl rewrite clappL eq = ⊥-elim (p x₁)
  headReduceLemma f x .(plug (snoc ctx x₁) (fromRedex r)) eq p
      | Redex×Context r .(snoc ctx x₁)
      | Snoc x₁ ctx rewrite snocClapp ctx x₁ (contract r)
      | snocClapp ctx x₁ (fromRedex r) with clappU eq
  ... | refl rewrite clappR eq | clappL eq | headReducePlug ctx r = refl

  -- Trivial case corresponding to performing beta reduction
  headReduceLemma2 : ∀ {Γ Γ₁ a b v}
                  → (body : ((a ⇒ b) ∷ Γ) ⊢ v)
                  → (env : Env Γ)
                  → (arg : (a ∷ Γ₁) ⊢ b)
                  → (env₂ : Env Γ₁)
                  → headReduce (Clapp (Closure (ƛ body) env)  (Closure (ƛ arg) env₂)) ≡ Closure body ( (Closure (ƛ arg) env₂) · env)
  headReduceLemma2 body env arg env₂ = refl


  -- Call by value dual
  headReduceLemma3 : ∀ {u v}
                  → (f : Closed (u ⇒ v))
                  → (x : Closed u)
                  → (fx : Closed v)
                  → (Clapp f x ≡ fx) 
                  → (isVal f)
                  → (isVal x → ⊥)
                  → headReduce fx ≡ Clapp f (headReduce x)
  headReduceLemma3 f x fx eq p1 p2 with decompose fx
  headReduceLemma3 f x .(plug ctx (fromRedex r)) eq p1 p2
      | Redex×Context r ctx with viewSnoc ctx
  headReduceLemma3 f x .(plug MT (fromRedex (Beta {Γ = _} {τ = _} {σ = _} x₁ x₂ (Val c x₃)))) eq p1 p2
      | Redex×Context (Beta x₁ x₂ (Val c x₃)) .MT
      | Nil  with clappU eq
  ... | refl rewrite clappR eq = ⊥-elim (p2 x₃)
  headReduceLemma3 f x .(plug (cons ctx (Val c x₁)) (fromRedex r)) eq p1 p2
      | Redex×Context r .(cons ctx (Val c x₁))
      | Cons (Val c x₁) ctx
    rewrite consClapp ctx c x₁ (contract r)
      | consClapp ctx c x₁ (fromRedex r) with clappU eq
  ... | refl rewrite clappL eq
      | clappR eq
      | headReducePlug ctx r = refl
  headReduceLemma3 f x .(plug (snoc ctx x₁) (fromRedex r)) eq p1 p2
      | Redex×Context r .(snoc ctx x₁)
      | Snoc x₁ ctx rewrite snocClapp ctx x₁ (contract r)
      | snocClapp ctx x₁ (fromRedex r) with clappU eq
  ... | refl rewrite clappL eq = ⊥-elim (plugLemma ctx r p1)

module IteratedHeadReduction where
  open Terms
  open Redex

  -- Bove-Capretta trace type
  data Trace : ∀ {u} → {c : Closed u} → Decomposition c → Set where
    Done : ∀ {u v Γ}
         → (body : (u ∷ Γ) ⊢ v)
         → (env : Env Γ)
         → Trace (Val body env)

    Step : {u v : Type}
           {r : Redex u}
           {ctx : EvalContext u v}
         → Trace (decompose (plug ctx (contract r)))
         → Trace (Redex×Context r ctx)

  -- It is structurally recursive, when we give it a Trace
  iterate : ∀ {u : Type}
          → {c : Closed u}
          → (d : Decomposition c)
          → Trace d
          → Value u
  iterate (Val body env) (Done .(body) .(env)) = Val (Closure (ƛ body) env) tt
  iterate {c} {u} (Redex×Context r ctx) (Step step) = iterate  (decompose ( plug ctx (contract r))) step


  -- Logical relation strenghtening the hypothesis, heeavily inspired by Girard "Proof and Types" proof of Normalization theorem
  Reducible : {u : Type}
            → (t : Closed u)
            → Set
            
  Reducible {●} t = Trace (decompose t)
  Reducible {u ⇒ v } t = Trace (decompose t) × (
    (x : Closed u) → Reducible x → Reducible (Clapp t x))

  getVal : ∀ {u}
         → (t : Closed u)
         → Reducible (t)
         → Value u
  getVal {●} t red = iterate ((decompose t)) red
  getVal {u ⇒ u₁} t (fst , snd) = iterate (decompose t) fst

  getTrace : ∀ {u}
           → {t : Closed u}
           → (red : Reducible t)
           → Trace (decompose t)
  getTrace {●} red = red
  getTrace {u ⇒ u₁} (fst , _) = fst



  -- Additional to show that environment of given closure is reducible
  ReducibleEnv : ∀ {Γ}
               → Env Γ
               → Set
               
  ReducibleEnv Nil = ⊤
  ReducibleEnv (x · env) = (Reducible x) × (ReducibleEnv env)

   -- Looking up from reducible environment gives reducible value
  deref : ∀ {Γ u}
          (env : Env Γ)
          (r : Γ ∋ u )
        → ReducibleEnv env
        → Reducible (env ! r)
  deref Nil () _
  deref (x · _) Z redEnv = proj₁ redEnv
  deref (_ · env) (S i) redEnv = deref env i (proj₂ redEnv)


  -- Useful in preservation lemma
  step : ∀ {u}
       → (c : Closed u)
       → (t : Trace (decompose (headReduce c)))
       → Trace (decompose c)
  step c trace with decompose c
  step ._ trace | Val body env =  Done body env
  step ._ trace | Redex×Context redex context = Step {r = redex} {ctx = context} trace

  -- For backwards preservation lemma
  unstep : ∀ {u}
         → (c : Closed u)
         → (t : Trace (decompose c))
         → (Trace (decompose (headReduce c)))
  unstep c trace with decompose ( c)
  unstep ._ trace | Val body env =  trace
  unstep .(plug context (fromRedex redex)) (Step trace) | Redex×Context redex context = trace


    -- Preservation lemma - inspired by Swierstra
  lemma1 : ∀ {u}
         → (t : Closed u)
         → (Reducible (headReduce t))
         → Reducible t
  lemma1 {●} t red = step t red
  lemma1 {u ⇒ u₁} (Closure (ƛ body) env) (fst , snd) = (Done body env , snd)
  lemma1 {u ⇒ u₁} (Closure (f ∘ arg) env) (fst , snd) = (step (Closure (f ∘ arg) env) fst , λ x redX → lemma1 (Clapp (Closure (f ∘ arg) env) x) (snd x redX))
  lemma1 {u ⇒ u₁} (Closure (` i) env) (fst , snd) = ( step (Closure (` i) env) (fst) , λ x red → lemma1 (Clapp (Closure (` i) env) x) (snd x red) )
  lemma1 {u ⇒ u₁} (Clapp f arg) (fst , snd) = (step (Clapp f arg) fst , λ y redY → lemma1 (Clapp (Clapp f arg) y) (forceStep y (snd y redY)))
    where
      forceStep : (y : Closed u)
                → Reducible (Clapp (headReduce (Clapp f arg)) y)
                → Reducible (headReduce (Clapp (Clapp f arg) y) )
      forceStep y h rewrite headReduceLemma (Clapp f arg) y (Clapp (Clapp f arg) y) refl id = h

  mutual
    -- Backwards preservation lemma - we have equivalence now
    lemma1converse : ∀ {u}
                     → (t : Closed u)
                     → (Reducible t)
                     → (Reducible (headReduce t))
    lemma1converse {●} t red = unstep t red
    lemma1converse {u ⇒ u₁} (Closure (ƛ body) env) (fst , snd) = (unstep (Closure ((ƛ body)) env) fst , snd)
    lemma1converse {u ⇒ u₁} (Closure (f ∘ arg) env) (fst , snd) = (unstep (Closure (f ∘ arg) env) fst , λ x redX → converseReducible (Closure (f ∘ arg) env) x id (snd x redX))
    lemma1converse {u ⇒ u₁} (Closure (` i) env) (fst , snd) = (unstep (Closure (` i) env) fst , λ x redX → converseReducible (Closure (` i) env) x id (snd x redX))
    lemma1converse {u ⇒ u₁} (Clapp t t₁) (fst , snd) = (unstep (Clapp t t₁) fst , λ x redX → converseReducible ((Clapp t t₁)) x id (snd x redX))

    -- helper function - we appeal to head reduction lemma to obtain necessary property
    converseReducible : ∀ {u v}
                      → (lhs : Closed (u ⇒ v))
                      → (x : Closed u)
                      → (proof : isVal lhs → ⊥)
                      → Reducible (Clapp lhs x)
                      → Reducible (Clapp (headReduce lhs) x)
    converseReducible lhs x proof red
      rewrite sym ( headReduceLemma lhs x (Clapp lhs x) refl proof) = lemma1converse ( (Clapp lhs x)) red

  mutual
    -- Stronger property needed in call-by-calue case - ie. partial BC trace implies reducibility of application of this thing to reducible function
    lemma3 : ∀ {Γ} {σ} {τ}
           → (body : (σ ∷ Γ) ⊢ τ)
           → (env : Env Γ)
           → (redEnv : ReducibleEnv env)
           → (x : Closed σ)
           → (d : Decomposition x)
           → (redX : Reducible x)
           → (trace : Trace (d))
           → Reducible (headReduce (Clapp (Closure (ƛ body) env) x))
    lemma3 body env redEnv .(Closure (ƛ body₁) env₁) .(Val body₁ env₁) redX (Done body₁ env₁) = lemma2 body (Closure (ƛ body₁) env₁ · env) (redX , redEnv)
    lemma3 body env redEnv closure (Redex×Context r c) redX (Step trace)
      rewrite (headReduceLemma3 (Closure (ƛ body) env) closure (Clapp (Closure (ƛ body) env) closure) refl tt (plugLemma c r) )
      rewrite sym (headReducePlug c r )
        = lemma1 (Clapp (Closure (ƛ body) env) (headReduce closure)) 
      (lemma3 body env redEnv (headReduce closure) (decompose (headReduce closure)) (lemma1converse closure redX) trace)

    -- Given a term and reducible environment, a closure of term in such environment is reducible - Substitution lemma (at least Girard names it that way)
    lemma2 : ∀ {Γ u}
             → (t : Γ ⊢ u)
             → (env : Env Γ)
             → (ReducibleEnv env)
             → Reducible (Closure t env)
    lemma2 (ƛ_ {Γ} {σ} {τ} body) env redEnv =
      (Done body env , λ x redX → lemma1 (Clapp (Closure (ƛ body) env) x) (lemma3 body env redEnv x (decompose x) redX (getTrace redX)))
    lemma2 (f ∘ x) env redEnv =
      let redF : Reducible (Closure f env)
          redF = lemma2 f env redEnv
      in let redX : Reducible (Closure x env)
             redX = lemma2 x env redEnv
      in lemma1 (Closure (f ∘ x) env) (proj₂ redF (Closure x env) (redX))
    lemma2 (` i) env redEnv =
      let redVar : Reducible (env ! i)
          redVar = deref env i redEnv
      in lemma1 (Closure (` i) env) redVar

  -- Termination property
  theorem : ∀ {u}
          → (t : [] ⊢ u)
          → Reducible (Closure t Nil)
  theorem t = lemma2 t Nil tt

  termination : ∀ {u}
              → (t : [] ⊢ u)
              → Trace (decompose (Closure t Nil))
  termination {●} t = theorem t
  termination {u ⇒ u₁} t = proj₁ (theorem t)

  evaluate : ∀ {u}
           → (t : [] ⊢ u)
           → (Value u)
  evaluate t = iterate (decompose (Closure t Nil)) (termination t)

-- Most of this secction strictly comes from Swierstra - it is independent of reduction order
module Refocusing where
  open Terms
  open Redex

 -- We can also use inline the calls to decompose'_aux, so we are left with a single function -- it still doesn't pass terminatiojn checker
  refocus : ∀ {u v}
          → (ctx : EvalContext u v)
          → (c : Closed u)
          → Decomposition (plug ctx c)

  refocus = Redex.decompose'

  -- Danvy's refocusing theorem - actually trivially stands by reflection
  refocusCorrect : ∀ { v u}
                   → (ctx : EvalContext u v)
                      (c : Closed u)
                   → refocus ctx c ≡ decompose (plug ctx c)
                   
  refocusCorrect MT (Closure (ƛ body) env) = refl
  refocusCorrect MT (Closure (term ∘ term₁) env) = refl
  refocusCorrect MT (Closure (` x) env) = refl
  refocusCorrect MT (Clapp closed closed₁) = refocusCorrect (ARG closed₁ MT) closed
  refocusCorrect (FN (Val (Closure (ƛ x) env₂ ) isval) context) (Closure (ƛ x₁) env)
    rewrite decomposePlug context (Clapp (Closure (ƛ x) env₂) (Closure (ƛ x₁) env)) = refl
  refocusCorrect (FN (Val (Closure (ƛ x) x₃) proof) context) (Closure (x₁ ∘ x₂) env)
    rewrite decomposePlug context (Clapp (Closure (ƛ x) x₃) (Closure (x₁ ∘ x₂) env)) = refl
  refocusCorrect (FN (Val (Closure (ƛ x) x₂) proof) context) (Closure (` x₁) env)
    rewrite decomposePlug context (Clapp (Closure (ƛ x) x₂) (Closure (` x₁) env)) = refl
  refocusCorrect (FN (Val (Closure (ƛ x) x₁) proof) context) (Clapp closed closed₁) =
    refocusCorrect (ARG closed₁ (FN (Val (Closure (ƛ x) x₁) proof) context)) closed
  refocusCorrect (ARG x context) (Closure (ƛ x₁) env)
    rewrite decomposePlug context (Clapp (Closure (ƛ x₁) env) x) = refl
  refocusCorrect (ARG x context) (Closure (x₁ ∘ x₂) env)
    rewrite decomposePlug context (Clapp (Closure (x₁ ∘ x₂ ) env) x) = refl
  refocusCorrect (ARG x context) (Closure (` x₁) env)
    rewrite decomposePlug context (Clapp (Closure (` x₁ ) env) x) = refl
  refocusCorrect (ARG x context) (Clapp closed closed₁) = refocusCorrect ((ARG closed₁ (ARG x context))) closed

  -- New Bove-Capretta trace (small change in Step - does refocus and contract) - sourced from Swierstra
  data Trace : {u : Type} {c : Closed u} → Decomposition c → Set where
      Done : ∀ {Γ u v}
           → (body : (u ∷ Γ) ⊢ v)
           → (env : Env Γ)
           ----------------------------
           → Trace (Val body env)

      Step : ∀ {u v}
           → {r : Redex u} {ctx : EvalContext u v}
           → Trace (refocus ctx (contract r))
           -------------------------------------------
           → Trace  (Redex×Context r ctx)


  -- given context, closure and trace obtained using decompose and plug we, we can get a trace based on refocusing
  rewriteStep : ∀ {u v}
                → (ctx : EvalContext u v)
                   (t : Closed u)
                → Trace (decompose (plug ctx t))
                -----------------------------
                → Trace (refocus ctx t)

  rewriteStep ctx term trace 
    rewrite refocusCorrect ctx term  = trace

  -- Given a closed term and old trace, we can produce new trace
  traceLemma : ∀ {u}
        → (t : Closed u)
        → IteratedHeadReduction.Trace (decompose t)
        ----------------------------------------------
        → Trace (decompose t)
  traceLemma t p with decompose t
  traceLemma ._ p | Val body env = Done body env
  traceLemma {u} .(plug ctx (fromRedex redex)) (IteratedHeadReduction.Step p) | Redex×Context redex ctx =
    Step {r = redex} {ctx = ctx} (rewriteStep ctx ((contract redex)) (traceLemma (plug ctx (contract redex)) p))

  termination : ∀ {u}
              → (t : [] ⊢ u)
              → Trace (refocus MT (Closure t Nil))
  termination t rewrite refocusCorrect MT (Closure t Nil) = traceLemma (Closure t Nil) (IteratedHeadReduction.termination t)

   --  Given a closed term, decomposition and trace we can "play" the evaluation from the trace to get to value
  iterate : ∀ {u}
          → {c : Closed u}
          → (d : Decomposition c)
          → Trace d
          → Value u
          
  iterate (Val body env) (Done .(body) .(env)) = Val (Closure (ƛ body) env) tt
  iterate (Redex×Context r ctx) (Step step) = iterate (refocus ctx (contract r)) step


  evaluate : ∀ {u}
           → (t : [] ⊢ u)
           → Value u
  evaluate t = iterate (refocus MT (Closure t Nil)) (termination t)

 -- Given old trace and new trace we can prove that iteration through both traces leads to the same result
  iterateLemma : ∀ {u}
                        → (t : Closed u)
                        → (t1 : Trace (decompose t))
                        → (t2 : IteratedHeadReduction.Trace (decompose t))
                        → iterate (decompose t) t1 ≡ IteratedHeadReduction.iterate (decompose t) t2

  iterateLemma t t1 t2 with decompose t
  iterateLemma .(Closure (ƛ body) env) (Done .body .env) (IteratedHeadReduction.Done .body .env) | Val body env = refl
  iterateLemma .(plug ctx (fromRedex r)) (Step t1) (IteratedHeadReduction.Step t2) | Redex×Context r ctx
    rewrite refocusCorrect ctx (contract r) = iterateLemma (plug ctx (contract r)) t1 t2

  -- Correctness proof - both evaluators reach the same result
  correctness : ∀ {u}
              → {t : Closed u}
              → (trace : Trace (refocus MT t))
              → (trace' : IteratedHeadReduction.Trace (decompose t))
              → iterate (refocus MT t) trace ≡ IteratedHeadReduction.iterate (decompose t) trace'
              
  correctness {u} {t} t1 t2 rewrite refocusCorrect MT t = iterateLemma t t1 t2

  -- Andn using a termination proof - we can say that both evaluators yield the same result

  corrolary : ∀ {u}
            → (t : [] ⊢ u)
            → evaluate t ≡ IteratedHeadReduction.evaluate t
  corrolary t = correctness (termination t) (IteratedHeadReduction.termination t)

-- CEK machine 
module Machine where
  open Terms
  open Redex

  -- Correctness of closure, environment, continuation is not dependent on reduction order - therefore adapted from Swierstra
  mutual
    -- Valid closures are those that aren't Clapp and their environment is correct
    isValidClosure : ∀ {u}
                   → Closed u
                   → Set
    isValidClosure (Closure x env) = isValidEnv env
    isValidClosure (Clapp closure closure₁) = ⊥

    -- Environment is correct if its empty, or it only contains correct closures
    isValidEnv : ∀ {Γ}
               → Env Γ
               → Set
    isValidEnv Nil = ⊤
    isValidEnv (x · env) = (isValidClosure x × isValidEnv env )

  -- Valid contexts are either MT, FN or ARG containing Closure not Clapp
  isValidContext : ∀ {u v}
                 → EvalContext u v
                 → Set
  isValidContext MT = ⊤
  isValidContext (FN (Val (Closure (ƛ body) env) proof) context)
    = ( isValidEnv env × isValidContext context )
  isValidContext (ARG (Closure x env) context) = ( isValidEnv env × isValidContext context )
  isValidContext (ARG (Clapp _ _) context) = ⊥

  -- Given a valid closure, we can unwrap its typing context
  getContext : ∀ {u}
             → Σ (Closed u) (isValidClosure)
             → Context
  getContext (Closure {Γ } _ _ , _) = Γ

  -- Given a valid closure, we can unwrap the substitution environment
  getEnv : ∀ {u}
         → (c : Σ (Closed u) (isValidClosure))
         → Env (getContext c)
  getEnv (Closure _ env , _) = env

  -- Given a valid closure of type u, we know that context of this closure entails u
  getTerm : ∀ {u}
          → (c : Σ (Closed u) isValidClosure)
          → (getContext c) ⊢ u
  getTerm (Closure x _ , _) = x

  -- Finally, given variable reference of type u, substitution environment (which is correct), we can look up from the subst environment to get a valid closure
  lookup : ∀ {u Γ}
         → Γ ∋ u
         → (env : Env Γ)
         → isValidEnv env
         → Σ (Closed u) isValidClosure
  lookup Z (Closure x env · _) (fst , _) = (Closure x env) , fst
  lookup (S ref) (x · env) (_ , snd) = lookup ref env snd

  -- Ant this is the same as just using lookup operator
  lookupClosure : ∀ {Γ u}
                → (env : Env Γ)
                → (i : Γ ∋ u)
                → (p : isValidEnv env)
                → env ! i ≡ Closure (getTerm (lookup i env p)) (getEnv (lookup i env p)) 
  lookupClosure (Closure x x₁ · env) Z (fst , snd) = refl
  lookupClosure (Closure x x₁ · env) (S ref) (fst , snd) = lookupClosure env ref snd

  -- And if we unwrap environment of looked up closure, then it is also correct
  lookupLemma : ∀ {u Γ}
              → (env : Env Γ)
              → (i : Γ ∋ u)
              → (p : isValidEnv env)
              → isValidEnv (getEnv (lookup i env p))

  lookupLemma (Closure _ _ · _) Z (fst , _ ) = fst
  lookupLemma (Closure _ _ · env) (S i) (_ , snd) = lookupLemma env i snd

  -- Bove-Capretta datatype for CEK machine trace - 4 transition + 1 terminal state
  -- De Bruijn indices + "corridor" transitions
  data Trace : ∀ {Γ u v} → (Γ ⊢ u) → Env Γ → EvalContext u v → Set where

    -- looking up a variable requires correct env - it doesn't mutate the kontinuation frame
    Lookup : ∀ {u v Γ}
           → {ctx : EvalContext u v}
              {env : Env Γ }
              (i : Γ ∋ u)
              (p : isValidEnv env)
           → let c = lookup i env p in
              Trace (getTerm c) (getEnv c) ctx → Trace (` i) env ctx


    -- when you get (ƛ body, env, MT) then we reached final state
    Done : ∀ {Γ u v}
         → {env : Env Γ}
            (body : (v ∷ Γ) ⊢ u)
         → Trace (ƛ body) env MT

    -- Similar to Krivine machine, evaluate LHS first
    Left : ∀ { u Γ v w}
         → {env : Env Γ}
            {ctx : EvalContext v w}
            (f : Γ ⊢ (u ⇒ v) )
            (x : Γ ⊢ u)
          → Trace f env (ARG (Closure x env) ctx) → Trace (f ∘ x) env ctx

    -- when reaching a value (in this language functions are only values), and we have ARG frame on top
    -- Change frame to FN
    Right : ∀ {u Γ Δ v w}
          → {env : Env Γ}
             {ctx : EvalContext v w}
          →  (env₂ : Env Δ)
          →  (body : (u ∷ Δ) ⊢ v)
          →  (x : Γ ⊢ u)
          → Trace x env (FN (Val (Closure (ƛ body) env₂) tt) ctx) → Trace (ƛ body) env₂ (ARG (Closure x env) ctx)

    -- beta reduction, requires an argument to be a evaluated function
    -- restores env but appends a closure with evaluated argument and its local env
    Beta : ∀ {Γ u a b w Δ}
         → {env : Env Γ}
         → (ctx : EvalContext u w)
         → (argBody : (a ∷ Δ) ⊢ b)
         → (argEnv : Env Δ)
         → (body : ( (a ⇒ b) ∷ Γ) ⊢ u)
         → Trace body (Closure (ƛ argBody) argEnv · env) ctx  → Trace (ƛ argBody) argEnv (FN (Val (Closure (ƛ body) env) tt) ctx)
         


  -- CEK transition function
  -- it is actually (kontinuation, code, env) → Val
  -- also it is total and terminates
  -- see: partiality is not an inherent part of implementing ASMs when using dependently typed language
  refocus : ∀ {Γ u v}
           → (ctx : EvalContext u v)
              (t :  Γ ⊢ u)
              (env : Env Γ)
           → Trace t env ctx
           → Value v

  refocus kont .(` i) env (Lookup i p trace) = 
    let c = (lookup i env p) in refocus kont (getTerm c) (getEnv c) trace 
  refocus .MT .(ƛ body) env (Done body) = Val (Closure (ƛ body) env) tt
  refocus kont .(f ∘ x) env (Left f x trace) = refocus (ARG (Closure x env) kont) f env trace
  refocus (ARG (Closure x argEnv) kont) .(ƛ body) env (Right .env body x trace) = refocus (FN (Val (Closure (ƛ body) env) tt) kont) x argEnv trace
  refocus (FN (Val (Closure (ƛ body) env₂) tt) ctx) .(ƛ argBody) env (Beta ctx argBody .env body trace) = refocus ctx body (Closure (ƛ argBody) env · env₂) trace


  -- If you give me code, env and kont, and it's execution trace
  -- than I can give you proof that those lead to the same results
  correctness : ∀ {u v Γ}
              → (ctx : EvalContext u v)
                 (t : Γ ⊢ u)
                 (env : Env Γ)
              → (t1 : Trace t env ctx)
              → (t2 : Refocusing.Trace (Refocusing.refocus ctx (Closure t env)))
              → refocus ctx t env t1 ≡ Refocusing.iterate (Refocusing.refocus ctx (Closure t env)) t2

  correctness kont .(` i) env (Lookup i p t1) (Refocusing.Step t2)
    rewrite lookupClosure env i p = 
      let c = lookup i env p in correctness kont (getTerm c) (getEnv c) t1 t2
  correctness .MT .(ƛ body) env (Done body) (Refocusing.Done .body .env) = refl
  correctness kont .(f ∘ x) env (Left f x t1) (Refocusing.Step t2) = correctness (ARG (Closure x env) kont) f env t1 t2
  correctness (ARG (Closure x env₂) kont) .(ƛ body) env (Right .env body x t1) t2 = correctness (FN (Val (Closure (ƛ body) env) tt) kont) x env₂ t1 t2
  correctness (FN (Val (Closure (ƛ body) env₂) tt) ctx) .(ƛ argBody) env (Beta ctx argBody .env body t1) (Refocusing.Step t2)
    = correctness ctx body (Closure (ƛ argBody) env · env₂) t1 t2

  -- It must be sat isfied on every stage of reduction
  invariant : ∀ {Γ u v}
            → EvalContext u v
            → Env Γ
            → Set

  invariant ctx env = isValidEnv env × isValidContext ctx

  -- Given kont, code, env and proof invariant is satisfied we can obtain a new tracce from refocccusing trace
  traceLemma : ∀ {Γ u v}
             → (ctx : EvalContext u v)
             → (t : Γ ⊢ u)
             → (env : Env Γ)
             → invariant ctx env
             → Refocusing.Trace (Refocusing.refocus ctx (Closure t env))
             → Trace t env ctx
  traceLemma MT (ƛ code) env (fst , snd) (Refocusing.Done .code .env) = Done code
  traceLemma (FN (Val (Closure (ƛ x₁) x₂) x) kont) (ƛ code) env (fst , snd) (Refocusing.Step t1)
    = Beta kont code env x₁ (traceLemma kont x₁ (Closure (ƛ code) env · x₂) ((fst , proj₁ snd) , proj₂ snd) t1)
  traceLemma (ARG (Closure (ƛ x) x₁) kont) (ƛ code) env (fst , snd) (Refocusing.Step t1)
    = Right env code (ƛ x) (traceLemma (FN (Val (Closure (ƛ code) env) tt) kont) (ƛ x) x₁ (( proj₁ snd , fst , proj₂ snd)) ((Refocusing.Step t1)))
  traceLemma (ARG (Closure (x ∘ x₂) x₁) kont) (ƛ code) env (fst , snd) (Refocusing.Step t1)
    = Right env code (x ∘ x₂) (traceLemma (FN (Val (Closure (ƛ code) env) tt) kont) (x ∘ x₂) x₁ ((proj₁ snd , fst , proj₂ snd)) ((Refocusing.Step t1 )))
  traceLemma (ARG (Closure (` x) x₁) kont) (ƛ code) env (fst , snd) (Refocusing.Step t1)
    = Right env code (` x) (traceLemma (FN (Val (Closure (ƛ code) env) tt) kont) (` x) x₁ ((proj₁ snd , fst , proj₂ snd)) ((Refocusing.Step t1)))
  traceLemma MT (code ∘ code₁) env (fst , snd) (Refocusing.Step t1)
    = Left code code₁ (traceLemma (ARG (Closure code₁ env) MT) code env (fst , fst , tt) t1)
  traceLemma (FN (Val (Closure (ƛ x₁) x₂) x) kont) (code ∘ code₁) env (fst , snd) (Refocusing.Step t1)
    = Left code code₁ (traceLemma (ARG (Closure code₁ env) (FN (Val (Closure (ƛ x₁) x₂) x) kont)) code env (fst , fst , snd) t1)
  traceLemma (ARG (Closure (ƛ x) x₁) kont) (code ∘ code₁) env (fst , snd) (Refocusing.Step t1)
    = Left code code₁ (traceLemma (ARG (Closure code₁ env) (ARG (Closure (ƛ x) x₁) kont)) code env (fst , fst , snd) t1)
  traceLemma (ARG (Closure (x ∘ x₂) x₁) kont) (code ∘ code₁) env (fst , snd) (Refocusing.Step t1)
    = Left code code₁ (traceLemma (ARG (Closure code₁ env) (ARG (Closure (x ∘ x₂) x₁) kont)) code env (fst , fst , snd) t1)
  traceLemma (ARG (Closure (` x) x₁) kont) (code ∘ code₁) env (fst , snd) (Refocusing.Step t1)
    = Left code code₁ (traceLemma (ARG (Closure code₁ env) (ARG (Closure (` x) x₁) kont)) code env (fst , fst , snd) t1)
  traceLemma MT (` x) env (fst , tt) (Refocusing.Step t1)
    rewrite lookupClosure env x fst
      = Lookup x fst (traceLemma MT (getTerm (lookup x env fst)) (getEnv (lookup x env fst)) (lookupLemma env x fst , tt) t1)
  traceLemma (FN (Val (Closure (ƛ x₂) x₃) x₁) kont) (` x) env (fst , snd) (Refocusing.Step t1)
    rewrite lookupClosure env x fst
      = Lookup x fst (traceLemma (FN (Val (Closure (ƛ x₂) x₃) x₁) kont) (getTerm (lookup x env fst)) (getEnv (lookup x env fst)) (( lookupLemma env x fst , snd )) t1)
  traceLemma (ARG (Closure (ƛ x₁) x₂) kont) (` x) env (fst , snd) (Refocusing.Step t1)
    rewrite lookupClosure env x fst
      = Lookup x fst (traceLemma (ARG (Closure (ƛ x₁) x₂) kont) (getTerm (lookup x env fst)) (getEnv (lookup x env fst)) ( lookupLemma env x fst , snd) t1)
  traceLemma (ARG (Closure (x₁ ∘ x₃) x₂) kont) (` x) env (fst , snd) (Refocusing.Step t1)
    rewrite lookupClosure env x fst
      = Lookup x fst (traceLemma (ARG (Closure (x₁ ∘ x₃) x₂) kont) (getTerm (lookup x env fst)) (getEnv (lookup x env fst)) (lookupLemma env x fst , snd) t1)
  traceLemma (ARG (Closure (` x₁) x₂) kont) (` x) env (fst , snd) (Refocusing.Step t1)
    rewrite lookupClosure env x fst =
      Lookup x fst (traceLemma (ARG (Closure (` x₁) x₂) kont) (getTerm (lookup x env fst)) (getEnv (lookup x env fst)) (lookupLemma env x fst , snd) t1)

  -- Using old termination proof and trace conversion, we can obtain new termination proof
  termination : ∀ {u}
              → (t : [] ⊢ u)
              → Trace t Nil MT
  termination t = traceLemma MT t Nil (tt , tt) (Refocusing.termination t)

  -- And using the termination proof, we can have new evaluator (note it takes terms, not closures)
  evaluate : ∀ {u}
           → [] ⊢ u
           → Value u
  evaluate t = refocus MT t Nil ((termination t))

  -- And finally, evaluating through CEK gives the same results as evaluating through refocusing
  corollary : ∀ {u}
            → (t : [] ⊢ u)
            → evaluate t ≡ Refocusing.evaluate t
  corollary t = correctness MT t Nil (termination t) (Refocusing.termination t)

