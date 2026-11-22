/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `85a3956f8d763f4003659b2ea871b54d9d9f711e`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Intrinsically typed simply typed lambda calculus
-/
module

public import Mathlib.Data.List.GetD

/-!
# Intrinsically typed simply typed lambda calculus

This file defines a de Bruijn presentation of the simply typed lambda calculus.
Variables and terms are indexed by their contexts and types, so ill-typed terms
cannot be represented.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

universe u

/-- Simple types over an arbitrary collection of base types. -/
inductive Ty (Base : Type u) where
  | base : Base → Ty Base
  | arr : Ty Base → Ty Base → Ty Base
  deriving DecidableEq, Repr

end Cslib.Languages.LambdaCalculus.Stlc

namespace CslibStlc

scoped notation:60 A:61 " ⇒ " B:60 => Cslib.Languages.LambdaCalculus.Stlc.Ty.arr A B

end CslibStlc

namespace Cslib.Languages.LambdaCalculus.Stlc

universe u

open scoped CslibStlc

/-- A well-typed de Bruijn variable. -/
inductive Var {Base : Type u} : List (Ty Base) → Ty Base → Type u where
  | zero {A : Ty Base} {Γ : List (Ty Base)} : Var (A :: Γ) A
  | succ {A B : Ty Base} {Γ : List (Ty Base)} : Var Γ A → Var (B :: Γ) A

/-- Intrinsically typed terms. -/
inductive Tm {Base : Type u} : List (Ty Base) → Ty Base → Type u where
  | var {A : Ty Base} {Γ : List (Ty Base)} : Var Γ A → Tm Γ A
  | app {A B : Ty Base} {Γ : List (Ty Base)} : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  | lam {A B : Ty Base} {Γ : List (Ty Base)} : Tm (A :: Γ) B → Tm Γ (A ⇒ B)

variable {Base : Type u}
variable {A B C : Ty Base}
variable {Γ Δ Ξ Ω : List (Ty Base)}

/-- Type-preserving variable renamings. -/
abbrev Ren {Base : Type u} (Γ Δ : List (Ty Base)) := ∀ {A}, Var Γ A → Var Δ A

/-- Type-preserving simultaneous substitutions. -/
abbrev Sub {Base : Type u} (Γ Δ : List (Ty Base)) := ∀ {A}, Var Γ A → Tm Δ A

namespace Var

/-- Identity renaming. -/
def id : Ren Γ Γ := fun x ↦ x

/-- Composition of renamings. -/
def comp (ρ : Ren Γ Δ) (σ : Ren Δ Ξ) : Ren Γ Ξ := fun x ↦ σ (ρ x)

/-- Extend a renaming under one binder. -/
def lift (ρ : Ren Γ Δ) : Ren (A :: Γ) (A :: Δ)
  | _, .zero => .zero
  | _, .succ x => .succ (ρ x)

@[simp] theorem lift_zero (ρ : Ren Γ Δ) : lift (A := A) ρ .zero = .zero := rfl

@[simp] theorem lift_succ (ρ : Ren Γ Δ) (x : Var Γ B) :
    lift (A := A) ρ (.succ x) = .succ (ρ x) := rfl

@[simp] theorem lift_id_apply (x : Var (A :: Γ) B) :
    lift (id : Ren Γ Γ) x = x := by cases x <;> rfl

theorem lift_comp_apply (ρ : Ren Γ Δ) (σ : Ren Δ Ξ) (x : Var (A :: Γ) B) :
    lift (comp ρ σ) x = comp (lift ρ) (lift σ) x := by cases x <;> rfl

end Var

namespace Tm

/-- Rename every free variable in a term. -/
def rename : {Γ Δ : List (Ty Base)} → Ren Γ Δ → {A : Ty Base} → Tm Γ A → Tm Δ A
  | _, _, ρ, _, .var x => .var (ρ x)
  | _, _, ρ, _, .app f a => .app (rename ρ f) (rename ρ a)
  | _, _, ρ, _, .lam body => .lam (rename (Var.lift ρ) body)

@[simp] theorem rename_var (ρ : Ren Γ Δ) (x : Var Γ A) :
    rename ρ (.var x) = .var (ρ x) := rfl

@[simp] theorem rename_app (ρ : Ren Γ Δ) (f : Tm Γ (A ⇒ B)) (a : Tm Γ A) :
    rename ρ (.app f a) = .app (rename ρ f) (rename ρ a) := rfl

@[simp] theorem rename_lam (ρ : Ren Γ Δ) (body : Tm (A :: Γ) B) :
    rename ρ (.lam body) = .lam (rename (Var.lift ρ) body) := rfl

theorem rename_congr {ρ σ : Ren Γ Δ} (h : ∀ {A} (x : Var Γ A), ρ x = σ x)
    (t : Tm Γ B) : rename ρ t = rename σ t := by
  induction t generalizing Δ with
  | var x => simp [h]
  | app f a ihf iha => simp [ihf h, iha h]
  | @lam A B Γ body ih =>
      simp only [rename_lam]
      congr 1
      apply ih
      intro C x
      cases x with
      | zero => rfl
      | succ x => simp [h]

@[simp] theorem rename_id (t : Tm Γ A) : rename Var.id t = t := by
  induction t with
  | var => rfl
  | app f a ihf iha => simp [ihf, iha]
  | @lam A B Γ body ih =>
      simp only [rename_lam]
      congr 1
      rw [rename_congr (fun x ↦ Var.lift_id_apply x)]
      exact ih

theorem rename_comp (ρ : Ren Γ Δ) (σ : Ren Δ Ξ) (t : Tm Γ A) :
    rename σ (rename ρ t) = rename (Var.comp ρ σ) t := by
  induction t generalizing Δ Ξ with
  | var => rfl
  | app f a ihf iha => simp [ihf, iha]
  | @lam A B Γ body ih =>
      simp only [rename_lam]
      congr 1
      rw [ih (ρ := Var.lift ρ) (σ := Var.lift σ)]
      apply rename_congr
      exact fun x ↦ (Var.lift_comp_apply ρ σ x).symm

/-- Weakening by one variable. -/
def weaken (t : Tm Γ A) : Tm (B :: Γ) A := rename .succ t

end Tm

end Cslib.Languages.LambdaCalculus.Stlc
