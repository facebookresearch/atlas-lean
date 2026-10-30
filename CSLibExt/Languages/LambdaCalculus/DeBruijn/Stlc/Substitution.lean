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
# Renaming and substitution for STLC
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Syntax

/-!
# Renaming and substitution for STLC

The algebra in this file is the infrastructure used by beta reduction.  The
fusion laws make explicit that lifting under binders commutes with renaming and
substitution.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A B C : Ty Base}
variable {Γ Δ Ξ : List (Ty Base)}

namespace Sub

/-- The identity substitution. -/
def id : Sub Γ Γ := fun x ↦ .var x

/-- Turn a renaming into a substitution. -/
def ofRen (ρ : Ren Γ Δ) : Sub Γ Δ := fun x ↦ .var (ρ x)

/-- Extend a substitution under one binder. -/
def lift (σ : Sub Γ Δ) : Sub (A :: Γ) (A :: Δ)
  | _, .zero => .var .zero
  | _, .succ x => Tm.weaken (σ x)

/-- Substitute the newest variable and leave all older variables unchanged. -/
def single (a : Tm Γ A) : Sub (A :: Γ) Γ
  | _, .zero => a
  | _, .succ x => .var x

@[simp] theorem lift_zero (σ : Sub Γ Δ) : lift (A := A) σ .zero = .var .zero := rfl

@[simp] theorem lift_succ (σ : Sub Γ Δ) (x : Var Γ B) :
    lift (A := A) σ (.succ x) = Tm.weaken (σ x) := rfl

@[simp] theorem single_zero (a : Tm Γ A) : single a .zero = a := rfl

@[simp] theorem single_succ (a : Tm Γ A) (x : Var Γ B) :
    single a (.succ x) = .var x := rfl

end Sub

namespace Tm

/-- Simultaneous capture-avoiding substitution. -/
def subst : {Γ Δ : List (Ty Base)} → Sub Γ Δ → {A : Ty Base} → Tm Γ A → Tm Δ A
  | _, _, σ, _, .var x => σ x
  | _, _, σ, _, .app f a => .app (subst σ f) (subst σ a)
  | _, _, σ, _, .lam body => .lam (subst (Sub.lift σ) body)

@[simp] theorem subst_var (σ : Sub Γ Δ) (x : Var Γ A) : subst σ (.var x) = σ x := rfl

@[simp] theorem subst_app (σ : Sub Γ Δ) (f : Tm Γ (A ⇒ B)) (a : Tm Γ A) :
    subst σ (.app f a) = .app (subst σ f) (subst σ a) := rfl

@[simp] theorem subst_lam (σ : Sub Γ Δ) (body : Tm (A :: Γ) B) :
    subst σ (.lam body) = .lam (subst (Sub.lift σ) body) := rfl

theorem subst_congr {σ τ : Sub Γ Δ} (h : ∀ {A} (x : Var Γ A), σ x = τ x)
    (t : Tm Γ B) : subst σ t = subst τ t := by
  induction t generalizing Δ with
  | var x => simp [h]
  | app f a ihf iha => simp [ihf h, iha h]
  | @lam A B Γ body ih =>
      simp only [subst_lam]
      congr 1
      apply ih
      intro C x
      cases x with
      | zero => rfl
      | succ x => simp [h]

@[simp] theorem subst_id (t : Tm Γ A) : subst Sub.id t = t := by
  induction t with
  | var => rfl
  | app f a ihf iha => simp [ihf, iha]
  | @lam A B Γ body ih =>
      simp only [subst_lam]
      have hlift : subst (Sub.lift (A := A) (Sub.id : Sub Γ Γ)) body =
          subst Sub.id body := subst_congr (fun x ↦ by cases x <;> rfl) body
      rw [hlift, ih]

theorem subst_ofRen (ρ : Ren Γ Δ) (t : Tm Γ A) :
    subst (Sub.ofRen ρ) t = rename ρ t := by
  induction t generalizing Δ with
  | var => rfl
  | app f a ihf iha => simp [ihf, iha]
  | @lam A B Γ body ih =>
      simp only [subst_lam, rename_lam]
      have hlift : subst (Sub.lift (A := A) (Sub.ofRen ρ)) body =
          subst (Sub.ofRen (Var.lift ρ)) body :=
        subst_congr (fun x ↦ by cases x <;> rfl) body
      rw [hlift, ih (ρ := Var.lift ρ)]

/-- Replace the newest free variable by `a`. -/
def instantiate (body : Tm (A :: Γ) B) (a : Tm Γ A) : Tm Γ B :=
  subst (Sub.single a) body

end Tm

end Cslib.Languages.LambdaCalculus.Stlc
