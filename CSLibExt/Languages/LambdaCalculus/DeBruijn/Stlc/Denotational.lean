/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Denotational semantics for STLC
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.BigStep

/-!
# Denotational semantics for STLC

Simple types are interpreted as Lean types and arrows as function spaces.
Terms are interpreted in type-indexed environments.  The main substitution
lemma shows that syntactic simultaneous substitution agrees with semantic
environment composition; beta reduction and all operational evaluation then
preserve denotation.

The construction follows the set-theoretic presentation in the
[PLFA Denotational chapter](https://plfa.github.io/Denotational/), specialized
to the intrinsically typed de Bruijn calculus developed in this directory.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u v

variable {Base : Type u}
variable {A B : Ty Base}
variable {Γ Δ : List (Ty Base)}
variable {I : Base → Type v}

namespace Ty

/-- Interpret base types by `I` and function types as Lean function spaces. -/
def denote (I : Base → Type v) : Ty Base → Type v
  | .base b => I b
  | .arr A B => denote I A → denote I B

@[simp] theorem denote_base (I : Base → Type v) (b : Base) : denote I (.base b) = I b := rfl

@[simp] theorem denote_arr (I : Base → Type v) (A B : Ty Base) :
    denote I (A ⇒ B) = (denote I A → denote I B) := rfl

end Ty

/-- A semantic environment assigns an element to every typed variable. -/
abbrev Env (I : Base → Type v) (Γ : List (Ty Base)) :=
  ∀ {A}, Var Γ A → Ty.denote I A

namespace Env

/-- Extend an environment with a value for the newest variable. -/
def cons (a : Ty.denote I A) (η : Env I Γ) : Env I (A :: Γ)
  | _, .zero => a
  | _, .succ x => η x

@[simp] theorem cons_zero (a : Ty.denote I A) (η : Env I Γ) : cons a η .zero = a := rfl

@[simp] theorem cons_succ (a : Ty.denote I A) (η : Env I Γ) (x : Var Γ B) :
    cons a η (.succ x) = η x := rfl

/-- Precompose an environment with a renaming. -/
def rename (ρ : Ren Γ Δ) (η : Env I Δ) : Env I Γ := fun x ↦ η (ρ x)

end Env

namespace Tm

/-- Interpret a well-typed term in a semantic environment. -/
def denote (I : Base → Type v) : {Γ : List (Ty Base)} → {A : Ty Base} →
    Tm Γ A → Env I Γ → Ty.denote I A
  | _, _, .var x, η => η x
  | _, _, .app f a, η => denote I f η (denote I a η)
  | _, _, .lam body, η => fun a ↦ denote I body (Env.cons a η)

@[simp] theorem denote_var (I : Base → Type v) (x : Var Γ A) (η : Env I Γ) :
    denote I (.var x) η = η x := rfl

@[simp] theorem denote_app (I : Base → Type v) (f : Tm Γ (A ⇒ B)) (a : Tm Γ A)
    (η : Env I Γ) : denote I (.app f a) η = denote I f η (denote I a η) := rfl

@[simp] theorem denote_lam (I : Base → Type v) (body : Tm (A :: Γ) B) (η : Env I Γ) :
    denote I (.lam body) η = fun a ↦ denote I body (Env.cons a η) := rfl

/-- Denotation commutes with variable renaming. -/
theorem denote_rename (I : Base → Type v) (ρ : Ren Γ Δ) (t : Tm Γ A) (η : Env I Δ) :
    denote I (rename ρ t) η = denote I t (Env.rename ρ η) := by
  induction t generalizing Δ with
  | var => rfl
  | app f a ihf iha => simp [ihf, iha]
  | @lam A B Γ body ih =>
      simp only [rename_lam, denote_lam]
      funext a
      rw [ih]
      apply congrArg (denote I body)
      funext C x
      cases x <;> rfl

/-- Weakening a term does not change its denotation in an extended environment. -/
theorem denote_weaken (I : Base → Type v) (t : Tm Γ A) (a : Ty.denote I B) (η : Env I Γ) :
    denote I (weaken (B := B) t) (Env.cons a η) = denote I t η := by
  rw [weaken, denote_rename]
  apply congrArg (denote I t)
  funext C x
  rfl

/-- Interpret every image of a syntactic substitution in an environment. -/
def denoteSub (I : Base → Type v) (σ : Sub Γ Δ) (η : Env I Δ) : Env I Γ :=
  fun x ↦ denote I (σ x) η

/-- Denotation commutes with simultaneous substitution. -/
theorem denote_subst (I : Base → Type v) (σ : Sub Γ Δ) (t : Tm Γ A) (η : Env I Δ) :
    denote I (subst σ t) η = denote I t (denoteSub I σ η) := by
  induction t generalizing Δ with
  | var => rfl
  | app f a ihf iha => simp [ihf, iha]
  | @lam A B Γ body ih =>
      simp only [subst_lam, denote_lam]
      funext a
      rw [ih]
      apply congrArg (denote I body)
      funext C x
      cases x with
      | zero => rfl
      | succ x => exact denote_weaken I (σ x) a η

/-- Instantiation is interpreted by extending the semantic environment. -/
theorem denote_instantiate (I : Base → Type v) (body : Tm (A :: Γ) B) (a : Tm Γ A)
    (η : Env I Γ) :
    denote I (instantiate body a) η = denote I body (Env.cons (denote I a η) η) := by
  rw [instantiate, denote_subst]
  apply congrArg (denote I body)
  funext C x
  cases x <;> rfl

end Tm

namespace Step

/-- One operational reduction preserves denotation. -/
theorem denote_eq (I : Base → Type v) {t t' : Tm Γ A} (h : Step t t') (η : Env I Γ) :
    Tm.denote I t η = Tm.denote I t' η := by
  induction h with
  | appFun hstep ih =>
      simp only [Tm.denote_app]
      rw [ih η]
  | appArg _ hstep ih =>
      simp only [Tm.denote_app]
      rw [ih η]
  | beta _ => exact (Tm.denote_instantiate I _ _ η).symm

end Step

namespace Steps

/-- Multi-step operational evaluation preserves denotation. -/
theorem denote_eq (I : Base → Type v) {t t' : Tm Γ A} (h : Steps t t') (η : Env I Γ) :
    Tm.denote I t η = Tm.denote I t' η := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (hstep.denote_eq I η)

end Steps

namespace Eval

/-- Big-step evaluation preserves denotation. -/
theorem denote_eq (I : Base → Type v) {t value : Tm Γ A} (h : Eval t value)
    (η : Env I Γ) : Tm.denote I t η = Tm.denote I value η :=
  h.to_steps.denote_eq I η

end Eval

end Cslib.Languages.LambdaCalculus.Stlc
