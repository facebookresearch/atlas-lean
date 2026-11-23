/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Adapted from https://github.com/anthropics/formal-math
at commit 16a5ce41304fcdaea4e0be7c132e1c361dc26da5,
eth/proof/rates/GeneralPieces/GenF/Borel.lean and Coeff.lean.
-/

/- Modifications copyright (c) Meta Platforms, Inc. and affiliates. -/
module

public import Mathlib.RingTheory.MvPowerSeries.Derivative

/-!
# Iterated partial derivatives of multivariate power series

`MvPowerSeries.iteratedPDeriv` differentiates in the order of a list, starting with its first
entry, as a linear map. Variable multiplicities use `Multiset.toFinsupp`. The coefficient
identities retain their factorial weights, including in positive characteristic.
-/

@[expose] public section

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

/-- Partial derivatives in list order, with the first entry applied first, as a linear map. -/
noncomputable def iteratedPDeriv (L : List σ) :
    MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R :=
  L.foldr (fun i D => D.comp (pderiv i).toLinearMap) LinearMap.id

@[simp]
theorem iteratedPDeriv_nil : iteratedPDeriv ([] : List σ) =
    (LinearMap.id : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R) := rfl

@[simp]
theorem iteratedPDeriv_cons (i : σ) (L : List σ) :
    iteratedPDeriv (R := R) (i :: L) = (iteratedPDeriv L).comp (pderiv i).toLinearMap := rfl

/-- Concatenating lists composes the second iterated derivative after the first. -/
theorem iteratedPDeriv_append (L K : List σ) :
    iteratedPDeriv (R := R) (L ++ K) = (iteratedPDeriv K).comp (iteratedPDeriv L) := by
  induction L with
  | nil => simp
  | cons i L ih => simp only [List.cons_append, iteratedPDeriv_cons, ih, LinearMap.comp_assoc]

/-- Two formal partial derivatives commute. -/
theorem pderiv_pderiv (i j : σ) (F : MvPowerSeries σ R) :
    pderiv i (pderiv j F) = pderiv j (pderiv i F) := by
  by_cases h : i = j
  · rw [h]
  · ext β
    rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv, add_right_comm,
      Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm h),
      Finsupp.single_eq_of_ne h, add_zero, add_zero]
    ring

/-- A partial derivative commutes with any list of partial derivatives. -/
theorem pderiv_iteratedPDeriv (i : σ) (L : List σ) (F : MvPowerSeries σ R) :
    pderiv i (iteratedPDeriv L F) = iteratedPDeriv L (pderiv i F) := by
  induction L generalizing F with
  | nil => rfl
  | cons j L ih =>
    change pderiv i (iteratedPDeriv L (pderiv j F)) =
      iteratedPDeriv L (pderiv j (pderiv i F))
    rw [ih, pderiv_pderiv]

end MvPowerSeries

/-- List variable multiplicities equal the sum of singleton multi-indices. -/
theorem Multiset.toFinsupp_coe_list_eq_sum {σ : Type*} [DecidableEq σ] (L : List σ) :
    Multiset.toFinsupp (L : Multiset σ) = (L.map fun i => Finsupp.single i 1).sum := by
  induction L with
  | nil => exact Multiset.toFinsupp_zero
  | cons i L ih =>
    rw [← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
      Multiset.toFinsupp_singleton, ih]
    simp

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

private theorem factorial_prod_add_single (β : σ →₀ ℕ) (i : σ) :
    (β + Finsupp.single i 1).prod (fun _ n => n.factorial) =
      (β i + 1) * β.prod (fun _ n => n.factorial) := by
  classical
  have hs : (β + Finsupp.single i 1).support ⊆ insert i β.support := by
    refine Finsupp.support_add.trans (Finset.union_subset (Finset.subset_insert _ _) ?_)
    exact Finsupp.support_single_subset.trans
      (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
  have key : ∀ γ : σ →₀ ℕ, γ.support ⊆ insert i β.support →
      γ.prod (fun _ n => n.factorial) = ∏ j ∈ insert i β.support, (γ j).factorial :=
    fun γ h => Finsupp.prod_of_support_subset γ h _ (fun _ _ => rfl)
  have he : ∏ j ∈ (insert i β.support).erase i,
      ((β + Finsupp.single i 1 : σ →₀ ℕ) j).factorial =
        ∏ j ∈ (insert i β.support).erase i, (β j).factorial := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj), add_zero]
  rw [key _ hs, key β (Finset.subset_insert _ _),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self i _),
    ← Finset.mul_prod_erase _ (fun j => (β j).factorial) (Finset.mem_insert_self i _), he,
    Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, mul_assoc]

private theorem factorial_smul_coeff_pderiv (β : σ →₀ ℕ) (i : σ)
    (F : MvPowerSeries σ R) :
    (β + Finsupp.single i 1).prod (fun _ n => n.factorial) •
        coeff (β + Finsupp.single i 1) F =
      β.prod (fun _ n => n.factorial) • coeff β (pderiv i F) := by
  rw [coeff_pderiv, factorial_prod_add_single, nsmul_eq_mul, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

open Classical in
/-- The factorial-weighted coefficient after iterated differentiation. No factorial is
cancelled, so this identity also holds in positive characteristic. -/
theorem factorial_smul_coeff_iteratedPDeriv (L : List σ) (β : σ →₀ ℕ)
    (F : MvPowerSeries σ R) :
    (β + Multiset.toFinsupp (L : Multiset σ)).prod (fun _ n => n.factorial) •
        coeff (β + Multiset.toFinsupp (L : Multiset σ)) F =
      β.prod (fun _ n => n.factorial) • coeff β (iteratedPDeriv L F) := by
  induction L generalizing β F with
  | nil => simp [Multiset.toFinsupp_zero]
  | cons i L ih =>
    rw [← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
      Multiset.toFinsupp_singleton]
    rw [← add_assoc, add_right_comm β (Finsupp.single i 1), factorial_smul_coeff_pderiv,
      ih]
    rfl

open Classical in
/-- A monomial's factorial times its coefficient is the constant coefficient of the
corresponding iterated partial derivative. -/
theorem factorial_smul_coeff_eq_constantCoeff_iteratedPDeriv (L : List σ)
    (F : MvPowerSeries σ R) :
    (Multiset.toFinsupp (L : Multiset σ)).prod (fun _ n => n.factorial) •
        coeff (Multiset.toFinsupp (L : Multiset σ)) F =
      constantCoeff (iteratedPDeriv L F) := by
  simpa only [zero_add, Finsupp.prod_zero_index, one_smul,
    coeff_zero_eq_constantCoeff] using factorial_smul_coeff_iteratedPDeriv L 0 F

variable [Algebra ℚ R]

open Classical in
/-- The source rational-factorial scalar equation, obtained by casting the natural
factorial product and its scalar action. -/
theorem factorial_smul_coeff_iteratedPDeriv_rat (L : List σ) (β : σ →₀ ℕ)
    (F : MvPowerSeries σ R) :
    (β + Multiset.toFinsupp (L : Multiset σ)).prod (fun _ n => (n.factorial : ℚ)) •
        coeff (β + Multiset.toFinsupp (L : Multiset σ)) F =
      β.prod (fun _ n => (n.factorial : ℚ)) • coeff β (iteratedPDeriv L F) := by
  simpa only [← Nat.cast_finsuppProd, Nat.cast_smul_eq_nsmul] using
    factorial_smul_coeff_iteratedPDeriv L β F

open Classical in
/-- The source rational-factorial constant coefficient equation. -/
theorem factorial_smul_coeff_eq_constantCoeff_iteratedPDeriv_rat (L : List σ)
    (F : MvPowerSeries σ R) :
    (Multiset.toFinsupp (L : Multiset σ)).prod (fun _ n => (n.factorial : ℚ)) •
        coeff (Multiset.toFinsupp (L : Multiset σ)) F =
      constantCoeff (iteratedPDeriv L F) := by
  simpa only [← Nat.cast_finsuppProd, Nat.cast_smul_eq_nsmul] using
    factorial_smul_coeff_eq_constantCoeff_iteratedPDeriv L F

end MvPowerSeries
