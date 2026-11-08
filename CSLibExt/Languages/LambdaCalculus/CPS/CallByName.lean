/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Call-by-name CPS translation of the simply typed lambda calculus
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Denotational

/-!
# Call-by-name CPS translation and its denotational correctness

Plotkin's call-by-name continuation-passing-style translation (*Call-by-name,
call-by-value and the λ-calculus*, TCS 1, 1975), typed, on the intrinsically
typed de Bruijn STLC of `../DeBruijn/Stlc/`. For a fixed answer type `R`:

* types: `⟦b⟧ = b` and `⟦A → B⟧ = C⟦A⟧ → C⟦B⟧`, where `C⟦A⟧ = (⟦A⟧ → R) → R`
  is the type of computations of type `A` (`cbnComp`);
* contexts: a variable of type `A` becomes a variable of type `C⟦A⟧`, so
  arguments are passed as unevaluated computations;
* terms: `⟦x⟧ = x`, `⟦λx. M⟧ = λk. k (λx. ⟦M⟧)`, and
  `⟦M N⟧ = λk. ⟦M⟧ (λm. m ⟦N⟧ k)`.

The translation is type preserving by construction, from `Tm Γ A` to
`Tm (Γ.map (cbnComp R)) (cbnComp R A)`.

Correctness is the call-by-name analogue of `Translation.lean`'s Meyer–Wand
theorem for the set-theoretic semantics (`cbn_correct`): when the environments
are related, the translation of `t` is a computation that passes one value,
related to the denotation of `t`, to every continuation. Values are related by
`CbnRel` (equality at base types; at `A → B`, related computations as arguments
give related computations as results), and computations by `CbnCompRel`. At
base types, running the translation with the identity continuation returns the
term's value (`cbn_denote_base_id`).
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc.CPS

open scoped CslibStlc

universe u v

variable {Base : Type u}

/-- The call-by-name CPS translation of types. -/
def cbnTy (R : Ty Base) : Ty Base → Ty Base
  | .base b => .base b
  | .arr A B => ((cbnTy R A ⇒ R) ⇒ R) ⇒ ((cbnTy R B ⇒ R) ⇒ R)

/-- Computations of type `A`: `(⟦A⟧ → R) → R`. -/
abbrev cbnComp (R : Ty Base) (A : Ty Base) : Ty Base := (cbnTy R A ⇒ R) ⇒ R

variable (R : Ty Base)

@[simp] theorem cbnTy_base (b : Base) : cbnTy R (.base b) = .base b := rfl

@[simp] theorem cbnTy_arr (A B : Ty Base) :
    cbnTy R (A ⇒ B) = cbnComp R A ⇒ cbnComp R B := rfl

/-- The translation of a variable: the same position in the translated
context, now holding a computation. -/
def cbnVar : {Γ : List (Ty Base)} → {A : Ty Base} →
    Var Γ A → Var (Γ.map (cbnComp R)) (cbnComp R A)
  | _, _, .zero => .zero
  | _, _, .succ x => .succ (cbnVar x)

/-- The call-by-name CPS translation of terms. -/
def cbn : {Γ : List (Ty Base)} → {A : Ty Base} →
    Tm Γ A → Tm (Γ.map (cbnComp R)) (cbnComp R A)
  | _, _, .var x => .var (cbnVar R x)
  | _, _, .lam body => .lam (.app (.var .zero) (Tm.weaken (.lam (cbn body))))
  | _, _, .app f a =>
      .lam (.app (Tm.weaken (cbn f))
        (.lam (.app (.app (.var .zero) (Tm.weaken (Tm.weaken (cbn a)))) (.var (.succ .zero)))))

section Equations

variable {Γ : List (Ty Base)} {A B : Ty Base}

@[simp] theorem cbnVar_zero : cbnVar R (.zero : Var (A :: Γ) A) = .zero := rfl

@[simp] theorem cbnVar_succ (x : Var Γ A) :
    cbnVar R (.succ x : Var (B :: Γ) A) = .succ (cbnVar R x) := rfl

@[simp] theorem cbn_var (x : Var Γ A) : cbn R (.var x) = .var (cbnVar R x) := rfl

@[simp] theorem cbn_lam (body : Tm (A :: Γ) B) :
    cbn R (.lam body) = .lam (.app (.var .zero) (Tm.weaken (.lam (cbn R body)))) := rfl

@[simp] theorem cbn_app (f : Tm Γ (A ⇒ B)) (a : Tm Γ A) :
    cbn R (.app f a) =
      .lam (.app (Tm.weaken (cbn R f))
        (.lam (.app (.app (.var .zero) (Tm.weaken (Tm.weaken (cbn R a))))
          (.var (.succ .zero))))) := rfl

end Equations

variable {I : Base → Type v}

/-- The logical relation between direct-style values of type `A` and values of
the call-by-name CPS type `⟦A⟧`: equality at base types; at function types,
an argument computation related to `a` yields a result computation that
passes one value related to `f a` to every continuation. -/
def CbnRel (I : Base → Type v) : (A : Ty Base) → Ty.denote I A → Ty.denote I (cbnTy R A) → Prop
  | .base _, a, a' => a = a'
  | .arr A B, f, g => ∀ a (c : Ty.denote I (cbnComp R A)),
      (∃ v, CbnRel I A a v ∧ ∀ k, c k = k v) →
        ∃ w, CbnRel I B (f a) w ∧ ∀ k, g c k = k w

/-- A computation is related to a direct-style value when it passes one
related value to every continuation. -/
def CbnCompRel (I : Base → Type v) (A : Ty Base) (a : Ty.denote I A)
    (c : Ty.denote I (cbnComp R A)) : Prop :=
  ∃ v, CbnRel R I A a v ∧ ∀ k, c k = k v

@[simp] theorem cbnRel_base (b : Base) (a : I b) (a' : Ty.denote I (cbnTy R (.base b))) :
    CbnRel R I (.base b) a a' ↔ a = a' := Iff.rfl

theorem cbnRel_arr (A B : Ty Base) (f : Ty.denote I (A ⇒ B))
    (g : Ty.denote I (cbnTy R (A ⇒ B))) :
    CbnRel R I (A ⇒ B) f g ↔
      ∀ a c, CbnCompRel R I A a c → CbnCompRel R I B (f a) (g c) := Iff.rfl

/-- Environments related variable by variable: each translated variable holds
a computation related to the direct-style value. -/
def CbnEnvRel {Γ : List (Ty Base)} (η : Env I Γ) (η' : Env I (Γ.map (cbnComp R))) : Prop :=
  ∀ {A} (x : Var Γ A), CbnCompRel R I A (η x) (η' (cbnVar R x))

theorem CbnEnvRel.cons {Γ : List (Ty Base)} {A : Ty Base} {η : Env I Γ}
    {η' : Env I (Γ.map (cbnComp R))} (hη : CbnEnvRel R η η') {a : Ty.denote I A}
    {c : Ty.denote I (cbnComp R A)} (ha : CbnCompRel R I A a c) :
    CbnEnvRel R (Env.cons a η) (Env.cons (Γ := Γ.map (cbnComp R)) c η') := by
  intro B x
  cases x with
  | zero => exact ha
  | succ x => exact hη x

/-- Denotational correctness of the call-by-name CPS translation: in related
environments, the translation of `t` is a computation related to the
denotation of `t`. -/
theorem cbn_correct {Γ : List (Ty Base)} {A : Ty Base} (t : Tm Γ A) {η : Env I Γ}
    {η' : Env I (Γ.map (cbnComp R))} (hη : CbnEnvRel R η η') :
    CbnCompRel R I A (Tm.denote I t η) (Tm.denote I (cbn R t) η') := by
  induction t with
  | var x => exact hη x
  | @lam A B Γ body ih =>
      refine ⟨Tm.denote I (.lam (cbn R body)) η', ?_, ?_⟩
      · intro a c hc
        exact ih (hη.cons R hc)
      · intro k
        exact congrArg k (Tm.denote_weaken I (.lam (cbn R body)) k η')
  | @app A B Γ f a ihf iha =>
      obtain ⟨vf, hf, hfk⟩ := ihf hη
      obtain ⟨w, hw, hwk⟩ := hf _ _ (iha hη)
      refine ⟨w, hw, fun k => ?_⟩
      have hwa : ∀ m : Ty.denote I (cbnTy R (A ⇒ B)),
          Tm.denote I (Tm.weaken (B := cbnTy R (A ⇒ B))
              (Tm.weaken (B := cbnTy R B ⇒ R) (cbn R a)))
            (Env.cons m (Env.cons k η')) = Tm.denote I (cbn R a) η' := fun m =>
        (Tm.denote_weaken I _ m (Env.cons k η')).trans (Tm.denote_weaken I (cbn R a) k η')
      have hstep : Tm.denote I (cbn R (.app f a)) η' k =
          Tm.denote I (cbn R f) η' (fun m => m (Tm.denote I (cbn R a) η') k) := by
        refine (congrFun (Tm.denote_weaken I (cbn R f) k η') _).trans ?_
        refine congrArg (Tm.denote I (cbn R f) η') (funext fun m => ?_)
        exact congrFun (congrArg m (hwa m)) k
      exact hstep.trans ((hfk _).trans (hwk k))

/-- At a base type, the translation passes exactly the term's value to the
continuation. -/
theorem cbn_denote_base {Γ : List (Ty Base)} {b : Base} (t : Tm Γ (.base b))
    {η : Env I Γ} {η' : Env I (Γ.map (cbnComp R))} (hη : CbnEnvRel R η η')
    (k : Ty.denote I (cbnTy R (.base b) ⇒ R)) :
    Tm.denote I (cbn R t) η' k = k (Tm.denote I t η) := by
  obtain ⟨v, hv, hk⟩ := cbn_correct R t hη
  rw [hk k]
  exact congrArg k hv.symm

/-- With the answer type equal to the term's base type, running the
translation with the identity continuation returns the term's value. -/
theorem cbn_denote_base_id {Γ : List (Ty Base)} {b : Base} (t : Tm Γ (.base b))
    {η : Env I Γ} {η' : Env I (Γ.map (cbnComp (.base b)))} (hη : CbnEnvRel (.base b) η η') :
    Tm.denote I (cbn (.base b) t) η' id = Tm.denote I t η :=
  cbn_denote_base (.base b) t hη id

end Cslib.Languages.LambdaCalculus.Stlc.CPS
