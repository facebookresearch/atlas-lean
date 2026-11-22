/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PCF: syntax and substitution
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Syntax

/-!
# PCF: syntax and substitution

Plotkin's PCF (*LCF considered as a programming language*, TCS 5, 1977) in the
presentation of Streicher (*Domain-Theoretic Foundations of Functional
Programming*, World Scientific, 2006): simple types over the single ground type
of natural numbers, with zero, successor, predecessor, a zero test at the
ground type, and a fixed-point combinator at every type.

Types and variables are those of the intrinsically typed de Bruijn STLC in
`../DeBruijn/Stlc/`, with the single base type `nat := .base ()`; the term type
`Tm Γ A` adds the PCF constants. Renaming and parallel substitution follow the
STLC development, together with the substitution algebra needed for the
operational and denotational metatheory.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.PCF

open scoped CslibStlc

/-- PCF types: simple types over the single ground type of naturals. -/
abbrev Ty := Stlc.Ty Unit

/-- The ground type of natural numbers. -/
abbrev Ty.nat : Ty := .base ()

/-- Typed de Bruijn variables, shared with the STLC. -/
abbrev Var := @Stlc.Var Unit

/-- Intrinsically typed PCF terms. -/
inductive Tm : List Ty → Ty → Type where
  | var {Γ : List Ty} {A : Ty} : Var Γ A → Tm Γ A
  | lam {Γ : List Ty} {A B : Ty} : Tm (A :: Γ) B → Tm Γ (A ⇒ B)
  | app {Γ : List Ty} {A B : Ty} : Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  | zero {Γ : List Ty} : Tm Γ .nat
  | succ {Γ : List Ty} : Tm Γ .nat → Tm Γ .nat
  | pred {Γ : List Ty} : Tm Γ .nat → Tm Γ .nat
  /-- `ifz t s₁ s₂` is `s₁` when `t` is zero and `s₂` when `t` is a successor. -/
  | ifz {Γ : List Ty} : Tm Γ .nat → Tm Γ .nat → Tm Γ .nat → Tm Γ .nat
  /-- The fixed-point combinator: `fix t` unfolds to `t (fix t)`. -/
  | fix {Γ : List Ty} {A : Ty} : Tm Γ (A ⇒ A) → Tm Γ A

variable {Γ Δ Ξ : List Ty} {A B : Ty}

/-- Type-preserving renamings. -/
abbrev Ren (Γ Δ : List Ty) := Stlc.Ren Γ Δ

/-- Type-preserving parallel substitutions. -/
abbrev Sub (Γ Δ : List Ty) := ∀ {A}, Var Γ A → Tm Δ A

namespace Tm

/-- The numeral `succⁿ zero`. -/
def numeral {Γ : List Ty} : Nat → Tm Γ .nat
  | 0 => .zero
  | n + 1 => .succ (numeral n)

@[simp] theorem numeral_zero : (numeral 0 : Tm Γ .nat) = .zero := rfl

@[simp] theorem numeral_succ (n : Nat) :
    (numeral (n + 1) : Tm Γ .nat) = .succ (numeral n) := rfl

/-- Distinct numbers give distinct numerals. -/
theorem numeral_injective : Function.Injective (numeral : Nat → Tm Γ .nat) := by
  intro m n h
  induction m generalizing n with
  | zero => cases n <;> simp_all [numeral]
  | succ m ih =>
      cases n with
      | zero => simp [numeral] at h
      | succ n =>
          simp only [numeral_succ, Tm.succ.injEq] at h
          rw [ih h]

/-- Rename the free variables of a term. -/
def rename : {Γ Δ : List Ty} → Ren Γ Δ → {A : Ty} → Tm Γ A → Tm Δ A
  | _, _, ρ, _, .var x => .var (ρ x)
  | _, _, ρ, _, .lam body => .lam (rename (Stlc.Var.lift ρ) body)
  | _, _, ρ, _, .app f a => .app (rename ρ f) (rename ρ a)
  | _, _, _, _, .zero => .zero
  | _, _, ρ, _, .succ t => .succ (rename ρ t)
  | _, _, ρ, _, .pred t => .pred (rename ρ t)
  | _, _, ρ, _, .ifz t s₁ s₂ => .ifz (rename ρ t) (rename ρ s₁) (rename ρ s₂)
  | _, _, ρ, _, .fix t => .fix (rename ρ t)

/-- Weakening by one variable. -/
def weaken (t : Tm Γ A) : Tm (B :: Γ) A := rename .succ t

section RenameEquations

variable (ρ : Ren Γ Δ)

@[simp] theorem rename_var (x : Var Γ A) : rename ρ (.var x) = .var (ρ x) := rfl
@[simp] theorem rename_lam (body : Tm (A :: Γ) B) :
    rename ρ (.lam body) = .lam (rename (Stlc.Var.lift ρ) body) := rfl
@[simp] theorem rename_app (f : Tm Γ (A ⇒ B)) (a : Tm Γ A) :
    rename ρ (.app f a) = .app (rename ρ f) (rename ρ a) := rfl
@[simp] theorem rename_zero : rename ρ (.zero : Tm Γ .nat) = .zero := rfl
@[simp] theorem rename_succ (t : Tm Γ .nat) : rename ρ (.succ t) = .succ (rename ρ t) := rfl
@[simp] theorem rename_pred (t : Tm Γ .nat) : rename ρ (.pred t) = .pred (rename ρ t) := rfl
@[simp] theorem rename_ifz (t s₁ s₂ : Tm Γ .nat) :
    rename ρ (.ifz t s₁ s₂) = .ifz (rename ρ t) (rename ρ s₁) (rename ρ s₂) := rfl
@[simp] theorem rename_fix (t : Tm Γ (A ⇒ A)) : rename ρ (.fix t) = .fix (rename ρ t) := rfl

end RenameEquations

theorem rename_congr {ρ ρ' : Ren Γ Δ} (h : ∀ {A} (x : Var Γ A), ρ x = ρ' x)
    (t : Tm Γ A) : rename ρ t = rename ρ' t := by
  induction t generalizing Δ with
  | var x => simp [h]
  | lam body ih =>
      simp only [rename]
      congr 1
      apply ih
      intro C x
      cases x with
      | zero => rfl
      | succ x => simp [h]
  | app f a ihf iha => simp [ihf h, iha h]
  | zero => rfl
  | succ t ih => simp [ih h]
  | pred t ih => simp [ih h]
  | ifz t s₁ s₂ iht ih₁ ih₂ => simp [iht h, ih₁ h, ih₂ h]
  | fix t ih => simp [ih h]

/-- The identity renaming. -/
@[simp] theorem rename_id (t : Tm Γ A) : rename (Stlc.Var.id : Ren Γ Γ) t = t := by
  induction t with
  | var => rfl
  | lam body ih =>
      simp only [rename_lam]
      congr 1
      rw [rename_congr (ρ' := Stlc.Var.id) (fun x => Stlc.Var.lift_id_apply x)]
      exact ih
  | app f a ihf iha => simp [ihf, iha]
  | zero => rfl
  | succ t ih => simp [ih]
  | pred t ih => simp [ih]
  | ifz t s₁ s₂ iht ih₁ ih₂ => simp [iht, ih₁, ih₂]
  | fix t ih => simp [ih]

theorem rename_rename (ρ : Ren Γ Δ) (ρ' : Ren Δ Ξ) (t : Tm Γ A) :
    rename ρ' (rename ρ t) = rename (fun x => ρ' (ρ x)) t := by
  induction t generalizing Δ Ξ with
  | var => rfl
  | lam body ih =>
      simp only [rename]
      congr 1
      rw [ih]
      apply rename_congr
      intro C x
      cases x <;> rfl
  | app f a ihf iha => simp [ihf, iha]
  | zero => rfl
  | succ t ih => simp [ih]
  | pred t ih => simp [ih]
  | ifz t s₁ s₂ iht ih₁ ih₂ => simp [iht, ih₁, ih₂]
  | fix t ih => simp [ih]

end Tm

namespace Sub

/-- The identity substitution. -/
def id : Sub Γ Γ := fun x => .var x

/-- Extend a substitution under one binder. -/
def lift (σ : Sub Γ Δ) : Sub (A :: Γ) (A :: Δ)
  | _, .zero => .var .zero
  | _, .succ x => Tm.weaken (σ x)

/-- Substitute for the newest variable, keeping the older ones. -/
def single (a : Tm Γ A) : Sub (A :: Γ) Γ
  | _, .zero => a
  | _, .succ x => .var x

/-- Extend a substitution with a term for a new newest variable. -/
def cons (a : Tm Δ A) (σ : Sub Γ Δ) : Sub (A :: Γ) Δ
  | _, .zero => a
  | _, .succ x => σ x

@[simp] theorem lift_zero (σ : Sub Γ Δ) : lift (A := A) σ .zero = .var .zero := rfl
@[simp] theorem lift_succ (σ : Sub Γ Δ) (x : Var Γ B) :
    lift (A := A) σ (.succ x) = Tm.weaken (σ x) := rfl
@[simp] theorem single_zero (a : Tm Γ A) : single a .zero = a := rfl
@[simp] theorem single_succ (a : Tm Γ A) (x : Var Γ B) : single a (.succ x) = .var x := rfl
@[simp] theorem cons_zero (a : Tm Δ A) (σ : Sub Γ Δ) : cons a σ .zero = a := rfl
@[simp] theorem cons_succ (a : Tm Δ A) (σ : Sub Γ Δ) (x : Var Γ B) :
    cons a σ (.succ x) = σ x := rfl

end Sub

namespace Tm

/-- Simultaneous capture-avoiding substitution. -/
def subst : {Γ Δ : List Ty} → Sub Γ Δ → {A : Ty} → Tm Γ A → Tm Δ A
  | _, _, σ, _, .var x => σ x
  | _, _, σ, _, .lam body => .lam (subst (Sub.lift σ) body)
  | _, _, σ, _, .app f a => .app (subst σ f) (subst σ a)
  | _, _, _, _, .zero => .zero
  | _, _, σ, _, .succ t => .succ (subst σ t)
  | _, _, σ, _, .pred t => .pred (subst σ t)
  | _, _, σ, _, .ifz t s₁ s₂ => .ifz (subst σ t) (subst σ s₁) (subst σ s₂)
  | _, _, σ, _, .fix t => .fix (subst σ t)

section SubstEquations

variable (σ : Sub Γ Δ)

@[simp] theorem subst_var (x : Var Γ A) : subst σ (.var x) = σ x := rfl
@[simp] theorem subst_lam (body : Tm (A :: Γ) B) :
    subst σ (.lam body) = .lam (subst (Sub.lift σ) body) := rfl
@[simp] theorem subst_app (f : Tm Γ (A ⇒ B)) (a : Tm Γ A) :
    subst σ (.app f a) = .app (subst σ f) (subst σ a) := rfl
@[simp] theorem subst_zero : subst σ (.zero : Tm Γ .nat) = .zero := rfl
@[simp] theorem subst_succ (t : Tm Γ .nat) : subst σ (.succ t) = .succ (subst σ t) := rfl
@[simp] theorem subst_pred (t : Tm Γ .nat) : subst σ (.pred t) = .pred (subst σ t) := rfl
@[simp] theorem subst_ifz (t s₁ s₂ : Tm Γ .nat) :
    subst σ (.ifz t s₁ s₂) = .ifz (subst σ t) (subst σ s₁) (subst σ s₂) := rfl
@[simp] theorem subst_fix (t : Tm Γ (A ⇒ A)) : subst σ (.fix t) = .fix (subst σ t) := rfl

@[simp] theorem subst_numeral (n : Nat) : subst σ (numeral n) = numeral n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

end SubstEquations

/-- Substitute `a` for the newest variable of `body`. -/
def instantiate (body : Tm (A :: Γ) B) (a : Tm Γ A) : Tm Γ B :=
  subst (Sub.single a) body

theorem subst_congr {σ τ : Sub Γ Δ} (h : ∀ {A} (x : Var Γ A), σ x = τ x)
    (t : Tm Γ A) : subst σ t = subst τ t := by
  induction t generalizing Δ with
  | var x => exact h x
  | lam body ih =>
      simp only [subst]
      congr 1
      apply ih
      intro C x
      cases x with
      | zero => rfl
      | succ x => simp [h]
  | app f a ihf iha => simp [ihf h, iha h]
  | zero => rfl
  | succ t ih => simp [ih h]
  | pred t ih => simp [ih h]
  | ifz t s₁ s₂ iht ih₁ ih₂ => simp [iht h, ih₁ h, ih₂ h]
  | fix t ih => simp [ih h]

@[simp] theorem subst_id (t : Tm Γ A) : subst Sub.id t = t := by
  induction t with
  | var => rfl
  | lam body ih =>
      simp only [subst]
      congr 1
      rw [subst_congr (τ := Sub.id) (fun x => by cases x <;> rfl)]
      exact ih
  | app f a ihf iha => simp [ihf, iha]
  | zero => rfl
  | succ t ih => simp [ih]
  | pred t ih => simp [ih]
  | ifz t s₁ s₂ iht ih₁ ih₂ => simp [iht, ih₁, ih₂]
  | fix t ih => simp [ih]

/-- A renaming followed by a substitution. -/
theorem subst_rename (ρ : Ren Γ Δ) (σ : Sub Δ Ξ) (t : Tm Γ A) :
    subst σ (rename ρ t) = subst (fun x => σ (ρ x)) t := by
  induction t generalizing Δ Ξ with
  | var => rfl
  | lam body ih =>
      simp only [rename, subst]
      congr 1
      rw [ih]
      apply subst_congr
      intro C x
      cases x <;> rfl
  | app f a ihf iha => simp [ihf, iha]
  | zero => rfl
  | succ t ih => simp [ih]
  | pred t ih => simp [ih]
  | ifz t s₁ s₂ iht ih₁ ih₂ => simp [iht, ih₁, ih₂]
  | fix t ih => simp [ih]

/-- A substitution followed by a renaming. -/
theorem rename_subst (σ : Sub Γ Δ) (ρ : Ren Δ Ξ) (t : Tm Γ A) :
    rename ρ (subst σ t) = subst (fun x => rename ρ (σ x)) t := by
  induction t generalizing Δ Ξ with
  | var => rfl
  | lam body ih =>
      simp only [rename, subst]
      congr 1
      rw [ih]
      apply subst_congr
      intro C x
      cases x with
      | zero => rfl
      | succ x =>
          simp only [Sub.lift_succ, weaken, rename_rename]
          rfl
  | app f a ihf iha => simp [ihf, iha]
  | zero => rfl
  | succ t ih => simp [ih]
  | pred t ih => simp [ih]
  | ifz t s₁ s₂ iht ih₁ ih₂ => simp [iht, ih₁, ih₂]
  | fix t ih => simp [ih]

/-- Composition of substitutions. -/
theorem subst_subst (σ : Sub Γ Δ) (τ : Sub Δ Ξ) (t : Tm Γ A) :
    subst τ (subst σ t) = subst (fun x => subst τ (σ x)) t := by
  induction t generalizing Δ Ξ with
  | var => rfl
  | lam body ih =>
      simp only [subst]
      congr 1
      rw [ih]
      apply subst_congr
      intro C x
      cases x with
      | zero => rfl
      | succ x =>
          simp only [Sub.lift_succ, weaken, subst_rename, rename_subst]
  | app f a ihf iha => simp [ihf, iha]
  | zero => rfl
  | succ t ih => simp [ih]
  | pred t ih => simp [ih]
  | ifz t s₁ s₂ iht ih₁ ih₂ => simp [iht, ih₁, ih₂]
  | fix t ih => simp [ih]

/-- Substituting under a binder and then instantiating the binder is
substitution with the extended substitution. -/
theorem instantiate_subst_lift (σ : Sub Γ Δ) (body : Tm (A :: Γ) B) (a : Tm Δ A) :
    (subst (Sub.lift σ) body).instantiate a = subst (Sub.cons a σ) body := by
  rw [instantiate, subst_subst]
  apply subst_congr
  intro C x
  cases x with
  | zero => rfl
  | succ x =>
      simp only [Sub.lift_succ, weaken, subst_rename, Sub.cons_succ]
      exact subst_id (σ x)

end Tm

end Cslib.Languages.LambdaCalculus.PCF
