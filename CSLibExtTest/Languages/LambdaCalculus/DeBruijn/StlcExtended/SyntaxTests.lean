/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.StlcExtended.Substitution

/-!
# Tests for the syntax and substitution of the extended simply typed lambda calculus

Concrete checks: decidable equality of types, weakening and renaming across the binders of case
analysis, substitution across the binder of `let` with a weakened replacement (and the captured
result it avoids), and instantiation of each binder former. Statement pins restate the renaming
and substitution laws and are closed by applying the declarations themselves, so a weakened or
drifted statement fails here.
-/

@[expose] public section

universe u

namespace Cslib.Languages.LambdaCalculus.StlcExtended.SyntaxTests

open Cslib.Languages.LambdaCalculus.StlcExtended
open scoped CslibStlcExtended

/-! ### Types -/

example : (Ty.prod .bool .unit : Ty Unit) ≠ .sum .bool .unit := by decide

example : (Ty.arr .bool (.prod .unit .bool) : Ty Unit) = (.bool ⇒ .prod .unit .bool) := rfl

/-! ### Weakening and renaming -/

/-- Weakening shifts a free variable past the new binder. -/
example : Tm.weaken (B := .unit) (.var .zero : Tm (Base := Unit) [.bool] .bool) =
    .var (.succ .zero) := rfl

/-- A case analysis in the context `[bool]` whose branches refer to the outer variable. -/
def caseOuter : Tm (Base := Unit) [.bool] .bool :=
  .case (.inl (B := .unit) .unit) (.var (.succ .zero)) (.var (.succ .zero))

/-- Weakening reaches into both branches of a case analysis and shifts only the outer variable:
the branch binders keep index `0`. -/
example : Tm.weaken (B := .bool) caseOuter =
    .case (.inl (B := .unit) .unit) (.var (.succ (.succ .zero))) (.var (.succ (.succ .zero))) :=
  rfl

/-- A case analysis whose branches use the payload bound by the branch. -/
def casePayload : Tm (Base := Unit) [.bool] (.sum .bool .unit) :=
  .case (.inl (B := .unit) (.var .zero)) (.inl (.var .zero)) (.inr (.var .zero))

/-- Renaming leaves the branch-bound variables in place. -/
example : Tm.weaken (B := .unit) casePayload =
    .case (.inl (.var (.succ .zero))) (.inl (.var .zero)) (.inr (.var .zero)) := rfl

/-! ### Substitution and instantiation -/

/-- Instantiating across the binder of `let`. In the body, index `0` is the `let`-bound variable,
index `1` the instantiated variable and index `2` the outer variable of the context `[bool]`. The
replacement `var 0` (the outer variable) is weakened to `var 1` under the `let` binder, so the
result is the same syntax in the smaller context. -/
example : Tm.instantiate
      (.letIn .tt (.ite (.var .zero) (.var (.succ .zero)) .ff) :
        Tm (Base := Unit) [.bool, .bool] .bool)
      (.var .zero) =
    .letIn .tt (.ite (.var .zero) (.var (.succ .zero)) .ff) := rfl

/-- The capture that substitution avoids: the replacement is not bound by the `let`. -/
example : Tm.instantiate
      (.letIn .tt (.ite (.var .zero) (.var (.succ .zero)) .ff) :
        Tm (Base := Unit) [.bool, .bool] .bool)
      (.var .zero) ≠
    .letIn .tt (.ite (.var .zero) (.var .zero) .ff) := by
  intro h
  cases h

/-- Instantiating a case analysis substitutes into the scrutinee and, through the lift, into both
branches: the payload bound by a branch (index `0`) stays, and the instantiated variable (index
`1` inside a branch) is replaced. -/
example : Tm.instantiate
      (.case (.var .zero) (.ite .tt .tt .ff) (.case (.var (.succ .zero)) .ff (.var .zero)) :
        Tm (Base := Unit) [.sum .unit .bool] .bool)
      (.inr .tt) =
    .case (.inr (A := .unit) .tt) (.ite .tt .tt .ff)
      (.case (.inr (A := .unit) .tt) .ff (.var .zero)) := rfl

/-- The single-variable substitution sends the newest variable to its argument and shifts the
others down. -/
example : (Sub.single (.tt : Tm (Base := Unit) [.unit] .bool)) .zero = .tt := rfl

example : (Sub.single (.tt : Tm (Base := Unit) [.unit] .bool)) (.succ .zero) = .var .zero := rfl

/-- Lifting a substitution keeps the newest variable and weakens the images of the others. -/
example : (Sub.lift (A := .bool) (Sub.single (.tt : Tm (Base := Unit) [] .bool))) (.succ .zero) =
    .tt := rfl

/-! ### Statement pins -/

section Pins

variable {Base : Type u} {A B : Ty Base} {Γ Δ Ξ : List (Ty Base)}

/-- Pin: the lift of the identity renaming. -/
theorem lift_id_apply_pin (x : Var (A :: Γ) B) : Var.lift (Var.id : Ren Γ Γ) x = x :=
  Var.lift_id_apply x

/-- Pin: lifting commutes with composition of renamings. -/
theorem lift_comp_apply_pin (ρ : Ren Γ Δ) (σ : Ren Δ Ξ) (x : Var (A :: Γ) B) :
    Var.lift (Var.comp ρ σ) x = Var.comp (Var.lift ρ) (Var.lift σ) x :=
  Var.lift_comp_apply ρ σ x

/-- Pin: renaming respects pointwise equality. -/
theorem rename_congr_pin {ρ σ : Ren Γ Δ} (h : ∀ {A} (x : Var Γ A), ρ x = σ x) (t : Tm Γ B) :
    Tm.rename ρ t = Tm.rename σ t :=
  Tm.rename_congr h t

/-- Pin: renaming along the identity. -/
theorem rename_id_pin (t : Tm Γ A) : Tm.rename Var.id t = t :=
  Tm.rename_id t

/-- Pin: renaming along a composite. -/
theorem rename_comp_pin (ρ : Ren Γ Δ) (σ : Ren Δ Ξ) (t : Tm Γ A) :
    Tm.rename σ (Tm.rename ρ t) = Tm.rename (Var.comp ρ σ) t :=
  Tm.rename_comp ρ σ t

/-- Pin: substitution respects pointwise equality. -/
theorem subst_congr_pin {σ τ : StlcExtended.Sub Γ Δ} (h : ∀ {A} (x : Var Γ A), σ x = τ x)
    (t : Tm Γ B) : Tm.subst σ t = Tm.subst τ t :=
  Tm.subst_congr h t

/-- Pin: substitution along the identity. -/
theorem subst_id_pin (t : Tm Γ A) : Tm.subst Sub.id t = t :=
  Tm.subst_id t

/-- Pin: substitution along a renaming. -/
theorem subst_ofRen_pin (ρ : Ren Γ Δ) (t : Tm Γ A) :
    Tm.subst (Sub.ofRen ρ) t = Tm.rename ρ t :=
  Tm.subst_ofRen ρ t

end Pins

end Cslib.Languages.LambdaCalculus.StlcExtended.SyntaxTests
