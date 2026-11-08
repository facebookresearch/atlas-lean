/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The simply typed lambda calculus with references: substitution laws
-/
module

public import CSLibExt.Languages.LambdaCalculus.References.Syntax

/-!
# Renaming and substitution laws

Constructor equations for `Term.rename` and `Term.subst`, and the laws of the
parallel renaming and substitution algebra: congruence, identity, composition
of renamings, and the interactions of renaming with substitution and of
substitution with itself.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.References

universe u

variable {Base : Type u}

namespace Term

section ConstructorEquations

variable (ρ : Nat → Nat) (σ : Nat → Term Base)

@[simp] theorem rename_var (x : Nat) : rename ρ (.var x : Term Base) = .var (ρ x) := rfl
@[simp] theorem rename_lam (T : Ty Base) (body : Term Base) :
    rename ρ (.lam T body) = .lam T (rename (liftRen ρ) body) := rfl
@[simp] theorem rename_app (f a : Term Base) :
    rename ρ (.app f a) = .app (rename ρ f) (rename ρ a) := rfl
@[simp] theorem rename_unit : rename ρ (.unit : Term Base) = .unit := rfl
@[simp] theorem rename_loc (l : Nat) : rename ρ (.loc l : Term Base) = .loc l := rfl
@[simp] theorem rename_ref (t : Term Base) : rename ρ (.ref t) = .ref (rename ρ t) := rfl
@[simp] theorem rename_deref (t : Term Base) : rename ρ (.deref t) = .deref (rename ρ t) := rfl
@[simp] theorem rename_assign (t₁ t₂ : Term Base) :
    rename ρ (.assign t₁ t₂) = .assign (rename ρ t₁) (rename ρ t₂) := rfl

@[simp] theorem subst_var (x : Nat) : subst σ (.var x) = σ x := rfl
@[simp] theorem subst_lam (T : Ty Base) (body : Term Base) :
    subst σ (.lam T body) = .lam T (subst (liftSub σ) body) := rfl
@[simp] theorem subst_app (f a : Term Base) :
    subst σ (.app f a) = .app (subst σ f) (subst σ a) := rfl
@[simp] theorem subst_unit : subst σ (.unit : Term Base) = .unit := rfl
@[simp] theorem subst_loc (l : Nat) : subst σ (.loc l : Term Base) = .loc l := rfl
@[simp] theorem subst_ref (t : Term Base) : subst σ (.ref t) = .ref (subst σ t) := rfl
@[simp] theorem subst_deref (t : Term Base) : subst σ (.deref t) = .deref (subst σ t) := rfl
@[simp] theorem subst_assign (t₁ t₂ : Term Base) :
    subst σ (.assign t₁ t₂) = .assign (subst σ t₁) (subst σ t₂) := rfl

end ConstructorEquations

/-- Renamings that agree pointwise act identically. -/
theorem rename_congr {ρ ρ' : Nat → Nat} (h : ∀ x, ρ x = ρ' x) (t : Term Base) :
    rename ρ t = rename ρ' t := by
  induction t generalizing ρ ρ' with
  | var x => simp [h]
  | lam T body ih =>
      simp only [rename_lam]
      congr 1
      apply ih
      intro x
      cases x <;> simp [h]
  | app f a ihf iha => simp [ihf h, iha h]
  | unit => rfl
  | loc => rfl
  | ref t ih => simp [ih h]
  | deref t ih => simp [ih h]
  | assign t₁ t₂ ih₁ ih₂ => simp [ih₁ h, ih₂ h]

/-- The identity renaming. -/
@[simp] theorem rename_id (t : Term Base) : rename id t = t := by
  induction t with
  | var => rfl
  | lam T body ih =>
      simp only [rename_lam]
      rw [rename_congr (ρ' := id) (fun x => by cases x <;> rfl)]
      rw [ih]
  | app f a ihf iha => simp [ihf, iha]
  | unit => rfl
  | loc => rfl
  | ref t ih => simp [ih]
  | deref t ih => simp [ih]
  | assign t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

/-- Composition of renamings. -/
theorem rename_rename (ρ ρ' : Nat → Nat) (t : Term Base) :
    rename ρ' (rename ρ t) = rename (ρ' ∘ ρ) t := by
  induction t generalizing ρ ρ' with
  | var => rfl
  | lam T body ih =>
      simp only [rename_lam, ih]
      congr 1
      apply rename_congr
      intro x
      cases x <;> rfl
  | app f a ihf iha => simp [ihf, iha]
  | unit => rfl
  | loc => rfl
  | ref t ih => simp [ih]
  | deref t ih => simp [ih]
  | assign t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

/-- Substitutions that agree pointwise act identically. -/
theorem subst_congr {σ σ' : Nat → Term Base} (h : ∀ x, σ x = σ' x) (t : Term Base) :
    subst σ t = subst σ' t := by
  induction t generalizing σ σ' with
  | var x => simp [h]
  | lam T body ih =>
      simp only [subst_lam]
      congr 1
      apply ih
      intro x
      cases x <;> simp [h]
  | app f a ihf iha => simp [ihf h, iha h]
  | unit => rfl
  | loc => rfl
  | ref t ih => simp [ih h]
  | deref t ih => simp [ih h]
  | assign t₁ t₂ ih₁ ih₂ => simp [ih₁ h, ih₂ h]

/-- The identity substitution. -/
@[simp] theorem subst_id (t : Term Base) : subst .var t = t := by
  induction t with
  | var => rfl
  | lam T body ih =>
      simp only [subst_lam]
      rw [subst_congr (σ' := .var) (fun x => by cases x <;> rfl)]
      rw [ih]
  | app f a ihf iha => simp [ihf, iha]
  | unit => rfl
  | loc => rfl
  | ref t ih => simp [ih]
  | deref t ih => simp [ih]
  | assign t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

/-- A renaming followed by a substitution is a substitution. -/
theorem subst_rename (ρ : Nat → Nat) (σ : Nat → Term Base) (t : Term Base) :
    subst σ (rename ρ t) = subst (σ ∘ ρ) t := by
  induction t generalizing ρ σ with
  | var => rfl
  | lam T body ih =>
      simp only [rename_lam, subst_lam, ih]
      congr 1
      apply subst_congr
      intro x
      cases x <;> rfl
  | app f a ihf iha => simp [ihf, iha]
  | unit => rfl
  | loc => rfl
  | ref t ih => simp [ih]
  | deref t ih => simp [ih]
  | assign t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

/-- A substitution followed by a renaming is a substitution. -/
theorem rename_subst (ρ : Nat → Nat) (σ : Nat → Term Base) (t : Term Base) :
    rename ρ (subst σ t) = subst (rename ρ ∘ σ) t := by
  induction t generalizing ρ σ with
  | var => rfl
  | lam T body ih =>
      simp only [rename_lam, subst_lam, ih]
      congr 1
      apply subst_congr
      intro x
      cases x with
      | zero => rfl
      | succ x =>
          simp only [Function.comp_apply, liftSub_succ, rename_rename]
          exact rename_congr (fun _ => rfl) _
  | app f a ihf iha => simp [ihf, iha]
  | unit => rfl
  | loc => rfl
  | ref t ih => simp [ih]
  | deref t ih => simp [ih]
  | assign t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

/-- Composition of substitutions. -/
theorem subst_subst (σ τ : Nat → Term Base) (t : Term Base) :
    subst τ (subst σ t) = subst (fun x => subst τ (σ x)) t := by
  induction t generalizing σ τ with
  | var => rfl
  | lam T body ih =>
      simp only [subst_lam, ih]
      congr 1
      apply subst_congr
      intro x
      cases x with
      | zero => rfl
      | succ x =>
          simp only [liftSub_succ, subst_rename, rename_subst]
          exact subst_congr (fun _ => rfl) _
  | app f a ihf iha => simp [ihf, iha]
  | unit => rfl
  | loc => rfl
  | ref t ih => simp [ih]
  | deref t ih => simp [ih]
  | assign t₁ t₂ ih₁ ih₂ => simp [ih₁, ih₂]

/-- Instantiating a weakened term gives back the term. -/
@[simp] theorem instantiate_rename_succ (t s : Term Base) :
    (rename Nat.succ t).instantiate s = t := by
  rw [instantiate, subst_rename]
  exact (subst_congr (fun _ => rfl) t).trans (subst_id t)

end Term

end Cslib.Languages.LambdaCalculus.References
