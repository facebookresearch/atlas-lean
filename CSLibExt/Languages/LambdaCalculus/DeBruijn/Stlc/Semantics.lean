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
# Call-by-value dynamics for STLC
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Substitution
public import Mathlib.Logic.Relation

/-!
# Call-by-value dynamics for STLC

This file gives the standard left-to-right call-by-value small-step semantics.
Because terms are intrinsically typed, every reduction rule preserves both its
context and its type by construction.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

/-- Lambda abstractions are the values of the pure calculus. -/
inductive Value {Base : Type u} : {Γ : List (Ty Base)} → {A : Ty Base} → Tm Γ A → Prop where
  | lam {A B : Ty Base} {Γ : List (Ty Base)} (body : Tm (A :: Γ) B) : Value (.lam body)

/-- Left-to-right call-by-value reduction. -/
inductive Step {Base : Type u} : {Γ : List (Ty Base)} → {A : Ty Base} →
    Tm Γ A → Tm Γ A → Prop where
  | appFun {A B : Ty Base} {Γ : List (Ty Base)} {f f' : Tm Γ (A ⇒ B)} {a : Tm Γ A} :
      Step f f' → Step (.app f a) (.app f' a)
  | appArg {A B : Ty Base} {Γ : List (Ty Base)} {f : Tm Γ (A ⇒ B)} {a a' : Tm Γ A} :
      Value f → Step a a' → Step (.app f a) (.app f a')
  | beta {A B : Ty Base} {Γ : List (Ty Base)} {body : Tm (A :: Γ) B} {a : Tm Γ A} :
      Value a → Step (.app (.lam body) a) (Tm.instantiate body a)

infix:50 " ⟶ₛ " => Step

variable {Base : Type u}
variable {A B C : Ty Base}
variable {Γ : List (Ty Base)}

namespace Value

theorem not_var (x : Var Γ A) : ¬Value (.var x) := by intro h; cases h

theorem not_app (f : Tm Γ (A ⇒ B)) (a : Tm Γ A) : ¬Value (.app f a) := by
  intro h
  cases h

end Value

namespace Step

/-- Values cannot reduce. -/
theorem value_irreducible {t t' : Tm Γ A} (hv : Value t) : ¬ t ⟶ₛ t' := by
  intro hs
  cases hv
  cases hs

/-- A closed function value is necessarily a lambda abstraction. -/
theorem closed_function_value_is_lam {f : Tm [] (A ⇒ B)} (hv : Value f) :
    ∃ body : Tm [A] B, f = .lam body := by
  cases hv with
  | lam body => exact ⟨body, rfl⟩

/-- A closed well-typed term is a value or can take a step. -/
theorem progress : {A : Ty Base} → (t : Tm [] A) → Value t ∨ ∃ t', t ⟶ₛ t'
  | _, .var x => nomatch x
  | _, .lam body => Or.inl (.lam body)
  | _, .app f a => by
      rcases progress f with hvf | ⟨f', hsf⟩
      · rcases progress a with hva | ⟨a', hsa⟩
        · obtain ⟨body, rfl⟩ := closed_function_value_is_lam hvf
          exact Or.inr ⟨Tm.instantiate body a, .beta hva⟩
        · exact Or.inr ⟨.app f a', .appArg hvf hsa⟩
      · exact Or.inr ⟨.app f' a, .appFun hsf⟩

/-- Call-by-value reduction is deterministic. -/
theorem deterministic {t t₁ t₂ : Tm Γ A} (h₁ : t ⟶ₛ t₁) (h₂ : t ⟶ₛ t₂) : t₁ = t₂ := by
  induction h₁ with
  | @appFun A B Γ f f' a hstep ih =>
      cases h₂ with
      | appFun hstep₂ => exact congrArg (fun g ↦ Tm.app g a) (ih hstep₂)
      | appArg hv hstep₂ => exact (value_irreducible hv hstep).elim
      | beta hva => cases hstep
  | @appArg A B Γ f a a' hv hstep ih =>
      cases h₂ with
      | appFun hstep₂ => exact (value_irreducible hv hstep₂).elim
      | appArg _ hstep₂ => exact congrArg (Tm.app f) (ih hstep₂)
      | beta hva => exact (value_irreducible hva hstep).elim
  | @beta A B Γ body a hva =>
      cases h₂ with
      | appFun hstep => cases hstep
      | appArg _ hstep => exact (value_irreducible hva hstep).elim
      | beta _ => rfl

/-- A term is in normal form when it has no outgoing reduction. -/
def NormalForm (t : Tm Γ A) : Prop := ∀ t', ¬t ⟶ₛ t'

/-- For closed well-typed terms, normal forms are exactly values. -/
theorem closed_normalForm_iff_value (t : Tm [] A) : NormalForm t ↔ Value t := by
  constructor
  · intro hnormal
    rcases progress t with hv | ⟨t', hstep⟩
    · exact hv
    · exact (hnormal t' hstep).elim
  · intro hv t' hstep
    exact value_irreducible hv hstep

end Step

/-- Reflexive transitive closure of evaluation. -/
abbrev Steps {Base : Type u} {Γ : List (Ty Base)} {A : Ty Base} :=
  Relation.ReflTransGen (@Step Base Γ A)

end Cslib.Languages.LambdaCalculus.Stlc
