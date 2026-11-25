/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRootExtraction

/-!
# Uniqueness of simple-root entries in Bruhat factors

Computes matrix entries under monomial conjugation. For two Bruhat
factorizations with the same middle factor, the relevant negative
permutation-order conditions force equality of the adjacent entries in their
upper factors.
-/

@[expose] public section

open Matrix
open Matrix.GeneralLinearGroup
open PermutationBilinearCocycle

namespace Matrix.GeneralLinearGroup

section MonomialConj

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R]

omit [DecidableEq ι] [Fintype ι] in
theorem monomialBase_inv_right (M : MonomialBase Rˣ ι) :
    M⁻¹.right = M.right⁻¹ :=
  rfl

omit [DecidableEq ι] [Fintype ι] in
theorem monomialBase_inv_left_apply (M : MonomialBase Rˣ ι) (k : ι) :
    M⁻¹.left k = (M.left (M.right k))⁻¹ := by
  cases M with
  | mk l r =>
    simp only [SemidirectProduct.inv_left, tupleActionHom_apply,
      permute_apply, Pi.inv_apply, inv_inv]

omit [DecidableEq ι] [Fintype ι] in
theorem monomialBase_inv_left_apply_inv (M : MonomialBase Rˣ ι) (j : ι) :
    M⁻¹.left (M.right⁻¹ j) = (M.left j)⁻¹ := by
  rw [monomialBase_inv_left_apply]; simp

omit [DecidableEq ι] [Fintype ι] in
theorem monomialBase_inv_left (M : MonomialBase Rˣ ι) :
    M⁻¹.left = permute M.right⁻¹ M.left⁻¹ := by
  ext k
  rw [monomialBase_inv_left_apply]
  simp [permute_apply, Pi.inv_apply]

theorem monomial_mul_matrix_entry
    (M : MonomialBase Rˣ ι) (U : Matrix ι ι R) (i j : ι) :
    ((monomialMatrixHom R ι M).val * U) i j =
      (M.left i : R) * U (M.right⁻¹ i) j := by
  classical
  have hEntry : ∀ k, (monomialMatrixHom R ι M).val i k =
      if M.right k = i then (M.left i : R) else 0 :=
    fun k => monomialMatrixHom_val_entry (R := R) M i k
  calc ((monomialMatrixHom R ι M).val * U) i j
      = ∑ k ∈ Finset.univ, (monomialMatrixHom R ι M).val i k * U k j := by
        simp [Matrix.mul_apply]
    _ = ∑ k ∈ Finset.univ, (if M.right k = i then (M.left i : R) else 0) * U k j := by
        apply Finset.sum_congr rfl; intro k _; rw [hEntry k]
    _ = ∑ k ∈ Finset.univ, if M.right k = i then (M.left i : R) * U k j else 0 := by
        apply Finset.sum_congr rfl; intro k _
        by_cases hk : M.right k = i <;> simp [hk]
    _ = (M.left i : R) * U (M.right⁻¹ i) j := by
        have hSingle : ∀ k ∈ Finset.univ, k ≠ M.right⁻¹ i →
            (if M.right k = i then (M.left i : R) * U k j else 0) = 0 := by
          intro k _ hk
          have hRk : M.right k ≠ i := by
            intro heq; exact hk (by calc k = M.right⁻¹ (M.right k) := by simp
              _ = M.right⁻¹ i := by rw [heq])
          simp [hRk]
        have hAt : (if M.right (M.right⁻¹ i) = i then
            (M.left i : R) * U (M.right⁻¹ i) j else 0) =
            (M.left i : R) * U (M.right⁻¹ i) j := by simp
        rw [Finset.sum_eq_single (M.right⁻¹ i) hSingle (by simp)]; exact hAt

theorem matrix_mul_monomial_entry
    (M : MonomialBase Rˣ ι) (U : Matrix ι ι R) (i j : ι) :
    (U * (monomialMatrixHom R ι M).val) i j =
      U i (M.right j) * (M.left (M.right j) : R) := by
  classical
  have hEntry : ∀ k, (monomialMatrixHom R ι M).val k j =
      if M.right j = k then (M.left (M.right j) : R) else 0 := by
    intro k
    have h := monomialMatrixHom_val_entry (R := R) M k j
    by_cases hk : M.right j = k
    · rw [ite_eq_left hk] at h ⊢
      calc (monomialMatrixHom R ι M).val k j = (M.left k : R) := h
        _ = (M.left (M.right j) : R) := by rw [← hk]
    · rw [ite_eq_right hk] at h ⊢; exact h
  calc (U * (monomialMatrixHom R ι M).val) i j
      = ∑ k ∈ Finset.univ, U i k * (monomialMatrixHom R ι M).val k j := by
        simp [Matrix.mul_apply]
    _ = ∑ k ∈ Finset.univ, U i k *
          (if M.right j = k then (M.left (M.right j) : R) else 0) := by
        apply Finset.sum_congr rfl; intro k _; rw [hEntry k]
    _ = ∑ k ∈ Finset.univ, if M.right j = k then
          U i k * (M.left (M.right j) : R) else 0 := by
        apply Finset.sum_congr rfl; intro k _
        by_cases hk : M.right j = k <;> simp [hk]
    _ = U i (M.right j) * (M.left (M.right j) : R) := by
        have hSingle : ∀ k ∈ Finset.univ, k ≠ M.right j →
            (if M.right j = k then U i k * (M.left (M.right j) : R) else 0) = 0 := by
          intro k _ hk; simp [Ne.symm hk]
        have hAt : (if M.right j = M.right j then
            U i (M.right j) * (M.left (M.right j) : R) else 0) =
            U i (M.right j) * (M.left (M.right j) : R) := by simp
        rw [Finset.sum_eq_single (M.right j) hSingle (by simp)]; exact hAt

theorem monomial_conj_entry
    (M : MonomialBase Rˣ ι) (U : Matrix ι ι R) (i j : ι) :
    ((monomialMatrixHom R ι M).val * U *
      (monomialMatrixHom R ι M⁻¹).val) i j =
      (M.left i : R) * U (M.right⁻¹ i) (M.right⁻¹ j) *
        ((M.left j)⁻¹ : Rˣ).val := by
  calc ((monomialMatrixHom R ι M).val * U *
        (monomialMatrixHom R ι M⁻¹).val) i j
      = ((monomialMatrixHom R ι M).val * U) i (M⁻¹.right j) *
          (M⁻¹.left (M⁻¹.right j) : R) := by
        rw [matrix_mul_monomial_entry M⁻¹ _ i j]
    _ = (M.left i : R) * U (M.right⁻¹ i) (M⁻¹.right j) *
          (M⁻¹.left (M⁻¹.right j) : R) := by
        rw [monomial_mul_matrix_entry M U i (M⁻¹.right j)]
    _ = (M.left i : R) * U (M.right⁻¹ i) (M.right⁻¹ j) *
          ((M.left j)⁻¹ : Rˣ).val := by
        rw [monomialBase_inv_right, monomialBase_inv_left_apply_inv]

theorem monomialGL_conj_entry
    (M : MonomialBase Rˣ ι) (U : GL ι R) (i j : ι) :
    ((monomialMatrixHom R ι M * U * (monomialMatrixHom R ι M)⁻¹).val : Matrix ι ι R) i j =
      (M.left i : R) * ((U : Matrix ι ι R) (M.right⁻¹ i) (M.right⁻¹ j)) *
        ((M.left j)⁻¹ : Rˣ).val := by
  have hInv : (monomialMatrixHom R ι M)⁻¹ = monomialMatrixHom R ι M⁻¹ := by
    rw [← map_inv]
  have hMat : ((monomialMatrixHom R ι M * U * (monomialMatrixHom R ι M)⁻¹).val : Matrix ι ι R) =
      (monomialMatrixHom R ι M).val * (U : Matrix ι ι R) *
        (monomialMatrixHom R ι M⁻¹).val := by rw [hInv]; simp [Units.val_mul]
  rw [hMat]; exact monomial_conj_entry M _ i j

theorem monomialGL_conj_inv_entry
    (M : MonomialBase Rˣ ι) (U : GL ι R) (i j : ι) :
    (((monomialMatrixHom R ι M)⁻¹ * U * monomialMatrixHom R ι M).val : Matrix ι ι R) i j =
      ((M⁻¹.left i : Rˣ) : R) * ((U : Matrix ι ι R) (M.right i) (M.right j)) *
        (M.left (M.right j) : R) := by
  have hInv : (monomialMatrixHom R ι M)⁻¹ = monomialMatrixHom R ι M⁻¹ := by
    rw [← map_inv]
  calc (((monomialMatrixHom R ι M)⁻¹ * U * monomialMatrixHom R ι M).val : Matrix ι ι R) i j
      = ((monomialMatrixHom R ι M⁻¹).val * (U : Matrix ι ι R) *
          (monomialMatrixHom R ι M).val) i j := by rw [hInv, Units.val_mul, Units.val_mul]
    _ = ((monomialMatrixHom R ι M⁻¹).val * (U : Matrix ι ι R)) i (M.right j) *
          (M.left (M.right j) : R) := by rw [matrix_mul_monomial_entry M _ i j]
    _ = (M⁻¹.left i : R) * ((U : Matrix ι ι R) (M⁻¹.right⁻¹ i) (M.right j)) *
          (M.left (M.right j) : R) := by rw [monomial_mul_matrix_entry M⁻¹ _ i (M.right j)]
    _ = ((M⁻¹.left i : Rˣ) : R) * ((U : Matrix ι ι R) (M.right i) (M.right j)) *
          (M.left (M.right j) : R) := by
        have hRI : M⁻¹.right⁻¹ i = M.right i := by
          calc M⁻¹.right⁻¹ i = (M.right⁻¹)⁻¹ i := by rw [monomialBase_inv_right]
            _ = M.right i := by simp
        rw [hRI]

end MonomialConj

section FactorUniqueness

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {F : Type*} [Field F]

theorem upperElementary_inv_mul_entry
    (L L' : upperElementarySubgroup ι F) {i j : ι} (hij : i ⋖ j) :
    ((L⁻¹ * L' : upperElementarySubgroup ι F) : GL ι F) i j =
      -((L : GL ι F) : Matrix ι ι F) i j +
        ((L' : GL ι F) : Matrix ι ι F) i j := by
  have hMul := upperElementary_covBy_mul_entry (R := F) L⁻¹ L' hij
  have hInv := upperElementary_covBy_inv_entry (R := F) L hij
  calc ((L⁻¹ * L' : upperElementarySubgroup ι F) : GL ι F) i j
      = (((L⁻¹ : upperElementarySubgroup ι F) : GL ι F) : Matrix ι ι F) i j +
          ((L' : GL ι F) : Matrix ι ι F) i j := hMul
    _ = -((L : GL ι F) : Matrix ι ι F) i j +
          ((L' : GL ι F) : Matrix ι ι F) i j := by rw [hInv]

theorem upperElementary_mul_inv_entry
    (R R' : upperElementarySubgroup ι F) {i j : ι} (hij : i ⋖ j) :
    ((R * R'⁻¹ : upperElementarySubgroup ι F) : GL ι F) i j =
      ((R : GL ι F) : Matrix ι ι F) i j -
        ((R' : GL ι F) : Matrix ι ι F) i j := by
  have hMul := upperElementary_covBy_mul_entry (R := F) R R'⁻¹ hij
  have hInv := upperElementary_covBy_inv_entry (R := F) R' hij
  calc ((R * R'⁻¹ : upperElementarySubgroup ι F) : GL ι F) i j
      = ((R : GL ι F) : Matrix ι ι F) i j +
          (((R'⁻¹ : upperElementarySubgroup ι F) : GL ι F) : Matrix ι ι F) i j := hMul
    _ = ((R : GL ι F) : Matrix ι ι F) i j -
          ((R' : GL ι F) : Matrix ι ι F) i j := by rw [hInv]; abel

theorem leftEntry_eq_of_factorization_eq_sameMiddle_of_invNeg
    {L R L' R' : upperElementarySubgroup ι F}
    {M : MonomialBase Fˣ ι}
    (hEq : (L : GL ι F) * monomialMatrixHom F ι M * (R : GL ι F) =
           (L' : GL ι F) * monomialMatrixHom F ι M * (R' : GL ι F))
    {i j : ι} (hij : i ⋖ j)
    (hNeg : M.right⁻¹ j < M.right⁻¹ i) :
    ((L : GL ι F) : Matrix ι ι F) i j = ((L' : GL ι F) : Matrix ι ι F) i j := by
  classical
  have hMid : ((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) *
      monomialMatrixHom F ι M =
      monomialMatrixHom F ι M *
        ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) := by
    have h1 : (L : GL ι F) * monomialMatrixHom F ι M * (R : GL ι F) *
        (R' : GL ι F)⁻¹ = (L' : GL ι F) * monomialMatrixHom F ι M := by
      calc (L : GL ι F) * monomialMatrixHom F ι M * (R : GL ι F) *
            (R' : GL ι F)⁻¹
          = ((L : GL ι F) * monomialMatrixHom F ι M * (R : GL ι F)) *
              (R' : GL ι F)⁻¹ := by rw [mul_assoc]
        _ = ((L' : GL ι F) * monomialMatrixHom F ι M * (R' : GL ι F)) *
              (R' : GL ι F)⁻¹ := by rw [hEq]
        _ = (L' : GL ι F) * monomialMatrixHom F ι M := by
            simp only [mul_assoc, mul_inv_cancel, mul_one]
    calc ((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) *
          monomialMatrixHom F ι M
        = (L : GL ι F)⁻¹ * ((L' : GL ι F) * monomialMatrixHom F ι M) := by
          rw [mul_assoc]
      _ = (L : GL ι F)⁻¹ *
            ((L : GL ι F) * monomialMatrixHom F ι M * (R : GL ι F) *
              (R' : GL ι F)⁻¹) := by rw [h1.symm]
      _ = monomialMatrixHom F ι M * (R : GL ι F) * (R' : GL ι F)⁻¹ := by
          simp only [← mul_assoc, inv_mul_cancel, one_mul]
      _ = monomialMatrixHom F ι M *
            ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) := by rw [mul_assoc]
  have hRearr : ((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) =
      monomialMatrixHom F ι M *
        ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) *
        (monomialMatrixHom F ι M)⁻¹ := by
    calc ((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F)
        = ((L : GL ι F)⁻¹ * (L' : GL ι F) *
            monomialMatrixHom F ι M) *
            (monomialMatrixHom F ι M)⁻¹ := by
          rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
      _ = (monomialMatrixHom F ι M *
            ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F)) *
            (monomialMatrixHom F ι M)⁻¹ := by rw [hMid]
      _ = _ := by rw [mul_assoc]
  have hEntryL : ((L⁻¹ * L' : upperElementarySubgroup ι F) : GL ι F) i j =
      -((L : GL ι F) : Matrix ι ι F) i j +
        ((L' : GL ι F) : Matrix ι ι F) i j :=
    upperElementary_inv_mul_entry L L' hij
  have hCoeLL' : ((L⁻¹ * L' : upperElementarySubgroup ι F) : GL ι F) =
      ((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) := by simp
  have hEntryL' : (((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) :
      Matrix ι ι F) i j =
      -((L : GL ι F) : Matrix ι ι F) i j +
        ((L' : GL ι F) : Matrix ι ι F) i j := by rw [← hCoeLL']; exact hEntryL
  have hEntryR : ((monomialMatrixHom F ι M *
      ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) *
      (monomialMatrixHom F ι M)⁻¹ : GL ι F) : Matrix ι ι F) i j =
      (M.left i : F) *
        (((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) : Matrix ι ι F)
          (M.right⁻¹ i) (M.right⁻¹ j) *
        ((M.left j)⁻¹ : Fˣ).val := by
    have hRR' : ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) =
        ((R * R'⁻¹ : upperElementarySubgroup ι F) : GL ι F) := by simp
    rw [hRR']; exact monomialGL_conj_entry M (R * R'⁻¹) i j
  have hZero : (((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) :
      Matrix ι ι F) (M.right⁻¹ i) (M.right⁻¹ j) = 0 := by
    have hMem : ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) ∈
        upperElementarySubgroup ι F :=
      Subgroup.mul_mem _ R.2 (Subgroup.inv_mem _ R'.2)
    exact upperElementary_isUpperTriangular_commRing ⟨_, hMem⟩ hNeg
  have hEqMat : (((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) : Matrix ι ι F) i j =
      ((monomialMatrixHom F ι M *
        ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) *
        (monomialMatrixHom F ι M)⁻¹ : GL ι F) : Matrix ι ι F) i j := by rw [hRearr]
  rw [hEntryL', hEntryR, hZero, mul_zero, zero_mul] at hEqMat
  have hAdd : -((L : GL ι F) : Matrix ι ι F) i j +
      ((L' : GL ι F) : Matrix ι ι F) i j = 0 := hEqMat
  calc ((L : GL ι F) : Matrix ι ι F) i j
      = ((L' : GL ι F) : Matrix ι ι F) i j -
          (-((L : GL ι F) : Matrix ι ι F) i j +
            ((L' : GL ι F) : Matrix ι ι F) i j) := by abel
    _ = ((L' : GL ι F) : Matrix ι ι F) i j - 0 := by rw [hAdd]
    _ = ((L' : GL ι F) : Matrix ι ι F) i j := by abel

theorem rightEntry_eq_of_factorization_eq_sameMiddle_of_permNeg
    {L R L' R' : upperElementarySubgroup ι F}
    {M : MonomialBase Fˣ ι}
    (hEq : (L : GL ι F) * monomialMatrixHom F ι M * (R : GL ι F) =
           (L' : GL ι F) * monomialMatrixHom F ι M * (R' : GL ι F))
    {i j : ι} (hij : i ⋖ j)
    (hNeg : M.right j < M.right i) :
    ((R : GL ι F) : Matrix ι ι F) i j =
      ((R' : GL ι F) : Matrix ι ι F) i j := by
  classical
  have hMid : ((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) *
      monomialMatrixHom F ι M =
      monomialMatrixHom F ι M *
        ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) := by
    have h1 : (L : GL ι F) * monomialMatrixHom F ι M * (R : GL ι F) *
        (R' : GL ι F)⁻¹ = (L' : GL ι F) * monomialMatrixHom F ι M := by
      calc (L : GL ι F) * monomialMatrixHom F ι M * (R : GL ι F) *
            (R' : GL ι F)⁻¹
          = ((L : GL ι F) * monomialMatrixHom F ι M * (R : GL ι F)) *
              (R' : GL ι F)⁻¹ := by rw [mul_assoc]
        _ = ((L' : GL ι F) * monomialMatrixHom F ι M * (R' : GL ι F)) *
              (R' : GL ι F)⁻¹ := by rw [hEq]
        _ = (L' : GL ι F) * monomialMatrixHom F ι M := by
            simp only [mul_assoc, mul_inv_cancel, mul_one]
    calc ((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) *
          monomialMatrixHom F ι M
        = (L : GL ι F)⁻¹ * ((L' : GL ι F) * monomialMatrixHom F ι M) := by
          rw [mul_assoc]
      _ = (L : GL ι F)⁻¹ *
            ((L : GL ι F) * monomialMatrixHom F ι M * (R : GL ι F) *
              (R' : GL ι F)⁻¹) := by rw [h1.symm]
      _ = monomialMatrixHom F ι M * (R : GL ι F) * (R' : GL ι F)⁻¹ := by
          simp only [← mul_assoc, inv_mul_cancel, one_mul]
      _ = monomialMatrixHom F ι M *
            ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) := by rw [mul_assoc]
  have hRearr : ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) =
      (monomialMatrixHom F ι M)⁻¹ *
        ((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) *
        monomialMatrixHom F ι M := by
    calc ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F)
        = 1 * ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) := by rw [one_mul]
      _ = ((monomialMatrixHom F ι M)⁻¹ * monomialMatrixHom F ι M) *
            ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) := by
          rw [inv_mul_cancel]
      _ = (monomialMatrixHom F ι M)⁻¹ *
            (monomialMatrixHom F ι M *
              ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F)) := by rw [mul_assoc]
      _ = (monomialMatrixHom F ι M)⁻¹ *
            (((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) *
              monomialMatrixHom F ι M) := by rw [← hMid]
      _ = (monomialMatrixHom F ι M)⁻¹ *
            ((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) *
            monomialMatrixHom F ι M := by rw [← mul_assoc]
  have hEntryR : ((R * R'⁻¹ : upperElementarySubgroup ι F) : GL ι F) i j =
      ((R : GL ι F) : Matrix ι ι F) i j -
        ((R' : GL ι F) : Matrix ι ι F) i j :=
    upperElementary_mul_inv_entry R R' hij
  have hCoeRR' : ((R * R'⁻¹ : upperElementarySubgroup ι F) : GL ι F) =
      ((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) := by simp
  have hEntryR' : (((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) :
      Matrix ι ι F) i j =
      ((R : GL ι F) : Matrix ι ι F) i j -
        ((R' : GL ι F) : Matrix ι ι F) i j := by rw [← hCoeRR']; exact hEntryR
  have hLL' : ((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) =
      ((L⁻¹ * L' : upperElementarySubgroup ι F) : GL ι F) := by simp
  have hEntryL : (((monomialMatrixHom F ι M)⁻¹ *
      ((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) *
      monomialMatrixHom F ι M : GL ι F) : Matrix ι ι F) i j =
      ((M⁻¹.left i : Fˣ) : F) *
        (((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) : Matrix ι ι F)
          (M.right i) (M.right j) *
        (M.left (M.right j) : F) := by
    calc (((monomialMatrixHom F ι M)⁻¹ *
          ((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) *
          monomialMatrixHom F ι M : GL ι F) : Matrix ι ι F) i j
        = (((monomialMatrixHom F ι M)⁻¹ *
            ((L⁻¹ * L' : upperElementarySubgroup ι F) : GL ι F) *
            monomialMatrixHom F ι M : GL ι F) : Matrix ι ι F) i j := by rw [hLL']
      _ = ((M⁻¹.left i : Fˣ) : F) *
            (((L⁻¹ * L' : upperElementarySubgroup ι F) : GL ι F) : Matrix ι ι F)
              (M.right i) (M.right j) *
            (M.left (M.right j) : F) := by
          exact monomialGL_conj_inv_entry M (L⁻¹ * L') i j
      _ = ((M⁻¹.left i : Fˣ) : F) *
            (((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) : Matrix ι ι F)
              (M.right i) (M.right j) *
            (M.left (M.right j) : F) := by rw [← hLL']
  have hZero : (((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) :
      Matrix ι ι F) (M.right i) (M.right j) = 0 := by
    have hMem : ((L⁻¹ * L' : upperElementarySubgroup ι F) : GL ι F) ∈
        upperElementarySubgroup ι F := (L⁻¹ * L').2
    have hEqMem : (((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) :
        Matrix ι ι F) (M.right i) (M.right j) =
        (((L⁻¹ * L' : upperElementarySubgroup ι F) : GL ι F) :
          Matrix ι ι F) (M.right i) (M.right j) := by rw [← hLL']
    rw [hEqMem]
    exact upperElementary_isUpperTriangular_commRing ⟨_, hMem⟩ hNeg
  have hEqMat : (((R : GL ι F) * (R' : GL ι F)⁻¹ : GL ι F) :
      Matrix ι ι F) i j =
      (((monomialMatrixHom F ι M)⁻¹ *
        ((L : GL ι F)⁻¹ * (L' : GL ι F) : GL ι F) *
        monomialMatrixHom F ι M : GL ι F) : Matrix ι ι F) i j := by rw [hRearr]
  rw [hEntryR', hEntryL, hZero, mul_zero, zero_mul] at hEqMat
  have hDiff : ((R : GL ι F) : Matrix ι ι F) i j -
      ((R' : GL ι F) : Matrix ι ι F) i j = 0 := hEqMat
  calc ((R : GL ι F) : Matrix ι ι F) i j
      = ((R' : GL ι F) : Matrix ι ι F) i j +
          (((R : GL ι F) : Matrix ι ι F) i j -
            ((R' : GL ι F) : Matrix ι ι F) i j) := by abel
    _ = ((R' : GL ι F) : Matrix ι ι F) i j + 0 := by rw [hDiff]
    _ = ((R' : GL ι F) : Matrix ι ι F) i j := by abel

end FactorUniqueness

section SLCorollaries

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {F : Type*} [Field F]

theorem SL_leftEntry_eq_bruhatLeft_of_invNeg
    {g : Matrix.SpecialLinearGroup ι F}
    {L R : upperElementarySubgroup ι F}
    {M : MonomialSL F ι}
    (hFact : g = UpperElementary.toSLHom L *
      monomialSLHom F ι M * UpperElementary.toSLHom R)
    {i j : ι} (hij : i ⋖ j)
    (hNeg : (M : MonomialBase Fˣ ι).right⁻¹ j <
      (M : MonomialBase Fˣ ι).right⁻¹ i) :
    ((L : GL ι F) : Matrix ι ι F) i j =
      ((bruhatLeft g : GL ι F) : Matrix ι ι F) i j := by
  classical
  have hMid : bruhatMiddle g = M :=
    bruhatMiddle_factorization_elim g L M R hFact
  have hCanon : g = UpperElementary.toSLHom (bruhatLeft g) *
      monomialSLHom F ι M * UpperElementary.toSLHom (bruhatRight g) := by
    calc g = UpperElementary.toSLHom (bruhatLeft g) *
            monomialSLHom F ι (bruhatMiddle g) *
            UpperElementary.toSLHom (bruhatRight g) := bruhat_factorizationSL g
      _ = _ := by rw [hMid]
  have hEqGL : (L : GL ι F) *
      monomialMatrixHom F ι (M : MonomialBase Fˣ ι) * (R : GL ι F) =
      (bruhatLeft g : GL ι F) *
        monomialMatrixHom F ι (M : MonomialBase Fˣ ι) *
        (bruhatRight g : GL ι F) := by
    have hToGL : (Matrix.SpecialLinearGroup.toGL g : GL ι F) =
        (L : GL ι F) *
          monomialMatrixHom F ι (M : MonomialBase Fˣ ι) * (R : GL ι F) := by
      calc (Matrix.SpecialLinearGroup.toGL g : GL ι F)
          = Matrix.SpecialLinearGroup.toGL
              (UpperElementary.toSLHom L *
                monomialSLHom F ι M * UpperElementary.toSLHom R) := by rw [← hFact]
        _ = _ := by simp [UpperElementary.toGL_toSLHom, monomialSLHom_toGL, map_mul]
    have hToGL2 : (Matrix.SpecialLinearGroup.toGL g : GL ι F) =
        (bruhatLeft g : GL ι F) *
          monomialMatrixHom F ι (M : MonomialBase Fˣ ι) *
          (bruhatRight g : GL ι F) := by
      calc (Matrix.SpecialLinearGroup.toGL g : GL ι F)
          = Matrix.SpecialLinearGroup.toGL
              (UpperElementary.toSLHom (bruhatLeft g) *
                monomialSLHom F ι M * UpperElementary.toSLHom (bruhatRight g)) := by
            rw [← hCanon]
        _ = _ := by simp [UpperElementary.toGL_toSLHom, monomialSLHom_toGL, map_mul]
    calc (L : GL ι F) * monomialMatrixHom F ι (M : MonomialBase Fˣ ι) * (R : GL ι F)
        = (Matrix.SpecialLinearGroup.toGL g : GL ι F) := hToGL.symm
      _ = _ := hToGL2
  exact leftEntry_eq_of_factorization_eq_sameMiddle_of_invNeg hEqGL hij hNeg

theorem SL_rightEntry_eq_bruhatRight_of_permNeg
    {g : Matrix.SpecialLinearGroup ι F}
    {L R : upperElementarySubgroup ι F}
    {M : MonomialSL F ι}
    (hFact : g = UpperElementary.toSLHom L *
      monomialSLHom F ι M * UpperElementary.toSLHom R)
    {i j : ι} (hij : i ⋖ j)
    (hNeg : (M : MonomialBase Fˣ ι).right j <
      (M : MonomialBase Fˣ ι).right i) :
    ((R : GL ι F) : Matrix ι ι F) i j =
      ((bruhatRight g : GL ι F) : Matrix ι ι F) i j := by
  classical
  have hMid : bruhatMiddle g = M :=
    bruhatMiddle_factorization_elim g L M R hFact
  have hCanon : g = UpperElementary.toSLHom (bruhatLeft g) *
      monomialSLHom F ι M * UpperElementary.toSLHom (bruhatRight g) := by
    calc g = UpperElementary.toSLHom (bruhatLeft g) *
            monomialSLHom F ι (bruhatMiddle g) *
            UpperElementary.toSLHom (bruhatRight g) := bruhat_factorizationSL g
      _ = _ := by rw [hMid]
  have hEqGL : (L : GL ι F) *
      monomialMatrixHom F ι (M : MonomialBase Fˣ ι) * (R : GL ι F) =
      (bruhatLeft g : GL ι F) *
        monomialMatrixHom F ι (M : MonomialBase Fˣ ι) *
        (bruhatRight g : GL ι F) := by
    have hToGL : (Matrix.SpecialLinearGroup.toGL g : GL ι F) =
        (L : GL ι F) * monomialMatrixHom F ι (M : MonomialBase Fˣ ι) * (R : GL ι F) := by
      calc (Matrix.SpecialLinearGroup.toGL g : GL ι F)
          = Matrix.SpecialLinearGroup.toGL
              (UpperElementary.toSLHom L * monomialSLHom F ι M * UpperElementary.toSLHom R) := by
            rw [← hFact]
        _ = _ := by simp [UpperElementary.toGL_toSLHom, monomialSLHom_toGL, map_mul]
    have hToGL2 : (Matrix.SpecialLinearGroup.toGL g : GL ι F) =
        (bruhatLeft g : GL ι F) * monomialMatrixHom F ι (M : MonomialBase Fˣ ι) *
          (bruhatRight g : GL ι F) := by
      calc (Matrix.SpecialLinearGroup.toGL g : GL ι F)
          = Matrix.SpecialLinearGroup.toGL
              (UpperElementary.toSLHom (bruhatLeft g) * monomialSLHom F ι M *
                UpperElementary.toSLHom (bruhatRight g)) := by rw [← hCanon]
        _ = _ := by simp [UpperElementary.toGL_toSLHom, monomialSLHom_toGL, map_mul]
    calc (L : GL ι F) * monomialMatrixHom F ι (M : MonomialBase Fˣ ι) * (R : GL ι F)
        = (Matrix.SpecialLinearGroup.toGL g : GL ι F) := hToGL.symm
      _ = _ := hToGL2
  exact rightEntry_eq_of_factorization_eq_sameMiddle_of_permNeg hEqGL hij hNeg

end SLCorollaries

end Matrix.GeneralLinearGroup

end
