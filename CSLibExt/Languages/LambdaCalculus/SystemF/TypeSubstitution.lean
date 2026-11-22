/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.SystemF.Syntax

/-! # Type-substitution algebra for impredicative System F -/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.SystemF

/-- Lifting the identity renaming gives the identity. -/
@[simp] theorem liftRen_id {n : Nat} :
    liftRen (id : Fin n → Fin n) = id := by
  funext i
  induction i using Fin.cases <;> rfl

/-- Lifting preserves composition of renamings. -/
theorem liftRen_comp {n k l : Nat} (ρ : Fin n → Fin k)
    (η : Fin k → Fin l) :
    liftRen (η ∘ ρ) = liftRen η ∘ liftRen ρ := by
  funext i
  induction i using Fin.cases <;> rfl

namespace Ty

/-- Type renaming by the identity does not change a type. -/
@[simp] theorem rename_id {n : Nat} (A : Ty n) : rename id A = A := by
  induction A with
  | var => rfl
  | arr A B ihA ihB => simp only [rename, ihA, ihB]
  | all B ih => simp only [rename, liftRen_id, ih]

/-- Two type renamings fuse into their composition. -/
theorem rename_comp {n k l : Nat} (ρ : Fin n → Fin k)
    (η : Fin k → Fin l) (A : Ty n) :
    rename η (rename ρ A) = rename (η ∘ ρ) A := by
  induction A generalizing k l with
  | var => rfl
  | arr A B ihA ihB => simp only [rename, ihA, ihB]
  | all B ih => simp only [rename, ih, ← liftRen_comp]

/-- Substitution after renaming composes the variable environments. -/
theorem subst_rename {n k l : Nat} (ρ : Fin n → Fin k)
    (σ : Fin k → Ty l) (A : Ty n) :
    subst σ (rename ρ A) = subst (σ ∘ ρ) A := by
  induction A generalizing k l with
  | var => rfl
  | arr A B ihA ihB => simp only [rename, subst, ihA, ihB]
  | all B ih =>
    simp only [rename, subst, ih]
    congr 2
    funext i
    induction i using Fin.cases <;> rfl

/-- Renaming after substitution renames each substituted image. -/
theorem rename_subst {n k l : Nat} (σ : Fin n → Ty k)
    (ρ : Fin k → Fin l) (A : Ty n) :
    rename ρ (subst σ A) = subst (fun i => rename ρ (σ i)) A := by
  induction A generalizing k l with
  | var => rfl
  | arr A B ihA ihB => simp only [rename, subst, ihA, ihB]
  | all B ih =>
    simp only [rename, subst, ih]
    congr 2
    funext i
    induction i using Fin.cases with
    | zero => rfl
    | succ i =>
      simp only [liftSub_succ, rename_comp]
      rfl

/-- Lifting the variable substitution gives the variable substitution. -/
@[simp] theorem liftSub_var {n : Nat} :
    liftSub (var : Fin n → Ty n) = var := by
  funext i
  induction i using Fin.cases <;> rfl

/-- Substitution of each type variable by itself is the identity. -/
@[simp] theorem subst_id {n : Nat} (A : Ty n) : subst var A = A := by
  induction A with
  | var => rfl
  | arr A B ihA ihB => simp only [subst, ihA, ihB]
  | all B ih => simp only [subst, liftSub_var, ih]

/-- A variable-valued substitution is the corresponding type renaming. -/
@[simp] theorem subst_var_rename {n k : Nat} (ρ : Fin n → Fin k)
    (A : Ty n) : subst (fun i => var (ρ i)) A = rename ρ A := by
  change subst (var ∘ ρ) A = rename ρ A
  rw [← subst_rename, subst_id]

/-- Lifted type substitution commutes with weakening an old type. -/
theorem subst_lift_rename {n k : Nat} (σ : Fin n → Ty k) (A : Ty n) :
    subst (liftSub σ) (rename Fin.succ A) =
      rename Fin.succ (subst σ A) := by
  rw [subst_rename]
  exact (rename_subst σ Fin.succ A).symm

/-- Two simultaneous type substitutions fuse by substituting each image. -/
theorem subst_comp {n k l : Nat} (σ : Fin n → Ty k)
    (τ : Fin k → Ty l) (A : Ty n) :
    subst τ (subst σ A) = subst (fun i => subst τ (σ i)) A := by
  induction A generalizing k l with
  | var => rfl
  | arr A B ihA ihB => simp only [subst, ihA, ihB]
  | all B ih =>
    simp only [subst, ih]
    congr 2
    funext i
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact subst_lift_rename τ (σ i)

/-- Type substitution commutes with discharging a type binder. -/
theorem subst_instantiate {n k : Nat} (σ : Fin n → Ty k)
    (B : Ty (n + 1)) (A : Ty n) :
    subst σ (instantiate B A) =
      instantiate (subst (liftSub σ) B) (subst σ A) := by
  simp only [instantiate, subst_comp]
  congr 1
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    change σ i = subst (Fin.cases (subst σ A) var)
      (rename Fin.succ (σ i))
    rw [subst_rename]
    exact (subst_id (σ i)).symm

/-- Instantiating a freshly weakened type restores the original type. -/
@[simp] theorem instantiate_rename {n : Nat} (B A : Ty n) :
    instantiate (rename Fin.succ B) A = B := by
  rw [instantiate, subst_rename]
  exact subst_id B

end Ty

end Cslib.Languages.LambdaCalculus.SystemF
