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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatMonomialUniqueness
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BruhatSimpleRoot
public import Mathlib.Order.Cover

@[expose] public section

open Matrix

namespace Matrix.GeneralLinearGroup

section CoverProduct

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {R : Type*} [CommRing R]

omit [DecidableEq ι] in
theorem isUpperTriangular_covBy_mul_entry
    {M N : Matrix ι ι R}
    (hM : IsUpperTriangular M) (hN : IsUpperTriangular N)
    (hM_diag : ∀ i, M i i = 1) (hN_diag : ∀ i, N i i = 1)
    {i j : ι} (hij : i ⋖ j) :
    (M * N) i j = M i j + N i j := by
  classical
  have hMul : (M * N) i j = ∑ k : ι, M i k * N k j := by
    simp [Matrix.mul_apply]
  rw [hMul]
  have h_i_ne_j : i ≠ j := hij.ne
  have h_eq :
      (∑ k : ι, M i k * N k j) =
        M i i * N i j + M i j * N j j +
          ∑ k ∈ (Finset.univ.erase i).erase j, M i k * N k j := by
    have h1 :
        (∑ k : ι, M i k * N k j) =
          ∑ k ∈ (Finset.univ : Finset ι), M i k * N k j := rfl
    rw [h1]
    have h2 :
        ∑ k ∈ (Finset.univ : Finset ι), M i k * N k j =
          M i i * N i j +
            ∑ k ∈ (Finset.univ : Finset ι).erase i, M i k * N k j := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [h2]
    have h3 :
        ∑ k ∈ (Finset.univ : Finset ι).erase i, M i k * N k j =
          M i j * N j j +
            ∑ k ∈ (Finset.univ.erase i).erase j, M i k * N k j := by
      rw [← Finset.add_sum_erase _ _
        (Finset.mem_erase.mpr ⟨h_i_ne_j.symm, Finset.mem_univ j⟩)]
    rw [h3]
    abel
  rw [h_eq, hM_diag i, hN_diag j, one_mul, mul_one]
  have hZero :
      ∑ k ∈ (Finset.univ.erase i).erase j, M i k * N k j = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk_ne_i : k ≠ i := by
      have h1 : k ∈ (Finset.univ : Finset ι).erase i := by
        exact Finset.mem_of_mem_erase hk
      exact (Finset.mem_erase.mp h1).1
    have hk_ne_j : k ≠ j :=
      (Finset.mem_erase.mp hk).1
    by_cases hk_lt_i : k < i
    · have hM0 : M i k = 0 := hM hk_lt_i
      simp [hM0]
    · have hi_lt_k : i < k := by
        have h_le : i ≤ k := not_lt.mp hk_lt_i
        rcases eq_or_lt_of_le h_le with heq | hlt
        · exact absurd heq.symm hk_ne_i
        · exact hlt
      by_cases hk_lt_j : k < j
      · exfalso
        exact hij.2 hi_lt_k hk_lt_j
      · have hj_lt_k : j < k := by
          have h_le : j ≤ k := not_lt.mp hk_lt_j
          rcases eq_or_lt_of_le h_le with heq | hlt
          · exact absurd heq.symm hk_ne_j
          · exact hlt
        have hN0 : N k j = 0 := hN hj_lt_k
        simp [hN0]
  rw [hZero, add_zero, add_comm]

omit [Fintype ι] in
theorem isUpperTriangular_covBy_one_entry
    {i j : ι} (hij : i ⋖ j) :
    (1 : Matrix ι ι R) i j = 0 := by
  have h_ne : i ≠ j := hij.ne
  simp [Matrix.one_apply, ite_eq_right h_ne]

theorem isUpperTriangular_covBy_inv_entry
    {M : Matrix ι ι R}
    (hM : IsUpperTriangular M) (hMi : ∀ i, M i i = 1)
    {Minv : Matrix ι ι R}
    (hM_inv_tri : IsUpperTriangular Minv)
    (hMinv_diag : ∀ i, Minv i i = 1)
    (hMul : M * Minv = 1) {i j : ι} (hij : i ⋖ j) :
    Minv i j = -M i j := by
  have hProd := isUpperTriangular_covBy_mul_entry hM hM_inv_tri hMi
    hMinv_diag hij
  have hOne : (M * Minv) i j = 0 := by
    rw [hMul]
    exact isUpperTriangular_covBy_one_entry hij
  rw [hProd] at hOne
  have hEq : M i j + Minv i j = 0 := hOne
  calc Minv i j = M i j + Minv i j - M i j := by abel
    _ = 0 - M i j := by rw [hEq]
    _ = -M i j := by abel

theorem upperUnitriangular_covBy_mul_entry
    (g h : upperUnitriangularSubgroup ι R) {i j : ι} (hij : i ⋖ j) :
    ((((g * h : upperUnitriangularSubgroup ι R) : GL ι R) :
        Matrix ι ι R) i j =
      ((((g : GL ι R) : Matrix ι ι R) i j +
        ((h : GL ι R) : Matrix ι ι R) i j))) := by
  have hM : IsUpperTriangular ((((g : GL ι R) : Matrix ι ι R))) := g.2.1
  have hN : IsUpperTriangular ((((h : GL ι R) : Matrix ι ι R))) := h.2.1
  have hM_diag : ∀ k, ((((g : GL ι R) : Matrix ι ι R) k k = 1)) := g.2.2
  have hN_diag : ∀ k, ((((h : GL ι R) : Matrix ι ι R) k k = 1)) := h.2.2
  have hMulMat :
      ((((g * h : upperUnitriangularSubgroup ι R) : GL ι R) :
          Matrix ι ι R) =
        ((((g : GL ι R) : Matrix ι ι R) *
          ((h : GL ι R) : Matrix ι ι R)))) := by simp
  rw [hMulMat]
  exact isUpperTriangular_covBy_mul_entry hM hN hM_diag hN_diag hij

theorem upperUnitriangular_covBy_one_entry
    {i j : ι} (hij : i ⋖ j) :
    ((((1 : upperUnitriangularSubgroup ι R) : GL ι R) :
        Matrix ι ι R) i j = 0) := by
  have h1 : ((((1 : upperUnitriangularSubgroup ι R) : GL ι R) :
      Matrix ι ι R) = (1 : Matrix ι ι R)) := by simp
  rw [h1]
  exact isUpperTriangular_covBy_one_entry hij

theorem upperUnitriangular_covBy_inv_entry
    (g : upperUnitriangularSubgroup ι R) {i j : ι} (hij : i ⋖ j) :
    ((((g⁻¹ : upperUnitriangularSubgroup ι R) : GL ι R) :
        Matrix ι ι R) i j =
      -((((g : GL ι R) : Matrix ι ι R) i j))) := by
  have hM : IsUpperTriangular ((((g : GL ι R) : Matrix ι ι R))) := g.2.1
  have hMi : ∀ k, ((((g : GL ι R) : Matrix ι ι R) k k = 1)) := g.2.2
  have hMinv : IsUpperTriangular
      (((((g⁻¹ : upperUnitriangularSubgroup ι R) : GL ι R) :
          Matrix ι ι R))) :=
    (g⁻¹ : upperUnitriangularSubgroup ι R).2.1
  have hMinv_diag : ∀ k,
      (((((g⁻¹ : upperUnitriangularSubgroup ι R) : GL ι R) :
          Matrix ι ι R) k k = 1)) :=
    (g⁻¹ : upperUnitriangularSubgroup ι R).2.2
  have hMul :
      ((((g : GL ι R) : Matrix ι ι R) *
        ((((g⁻¹ : upperUnitriangularSubgroup ι R) : GL ι R) :
            Matrix ι ι R)) = 1)) := by
    have hGL : (g : GL ι R) * ((g⁻¹ : upperUnitriangularSubgroup ι R) :
        GL ι R) = 1 := by
      have h1 : ((g⁻¹ : upperUnitriangularSubgroup ι R) : GL ι R) =
          (g : GL ι R)⁻¹ := rfl
      rw [h1, mul_inv_cancel]
    calc ((((g : GL ι R) : Matrix ι ι R) *
        ((((g⁻¹ : upperUnitriangularSubgroup ι R) : GL ι R) :
            Matrix ι ι R))))
        = ((((g : GL ι R) *
            ((g⁻¹ : upperUnitriangularSubgroup ι R) : GL ι R) :
              GL ι R).val : Matrix ι ι R)) := by simp
      _ = ((((1 : GL ι R).val : Matrix ι ι R))) := by rw [hGL]
      _ = 1 := by simp
  exact isUpperTriangular_covBy_inv_entry hM hMi hMinv hMinv_diag hMul hij

/-- Additive coefficient homomorphism for a simple-root cover entry. -/
def upperUnitriangularCoverCoeffHom
    (i j : ι) (hij : i ⋖ j) :
    upperUnitriangularSubgroup ι R →* Multiplicative R where
  toFun g := Multiplicative.ofAdd ((((g : GL ι R) : Matrix ι ι R) i j))
  map_one' := by
    have h0 := upperUnitriangular_covBy_one_entry (R := R) hij
    calc Multiplicative.ofAdd
          ((((1 : upperUnitriangularSubgroup ι R) : GL ι R) :
              Matrix ι ι R) i j)
        = Multiplicative.ofAdd (0 : R) := by rw [h0]
      _ = 1 := rfl
  map_mul' g h := by
    have hEq := upperUnitriangular_covBy_mul_entry g h hij
    calc Multiplicative.ofAdd
          ((((g * h : upperUnitriangularSubgroup ι R) : GL ι R) :
              Matrix ι ι R) i j)
        = Multiplicative.ofAdd
            ((((g : GL ι R) : Matrix ι ι R) i j +
              ((h : GL ι R) : Matrix ι ι R) i j)) := by rw [hEq]
      _ = Multiplicative.ofAdd ((((g : GL ι R) : Matrix ι ι R) i j)) *
          Multiplicative.ofAdd ((((h : GL ι R) : Matrix ι ι R) i j)) := rfl

@[simp]
theorem upperUnitriangularCoverCoeffHom_apply
    (i j : ι) (hij : i ⋖ j) (g : upperUnitriangularSubgroup ι R) :
    (upperUnitriangularCoverCoeffHom (R := R) i j hij g).toAdd =
      ((((g : GL ι R) : Matrix ι ι R) i j)) := rfl

theorem upperUnitriangularCoverCoeffHom_inv
    (i j : ι) (hij : i ⋖ j) (g : upperUnitriangularSubgroup ι R) :
    (upperUnitriangularCoverCoeffHom i j hij g⁻¹).toAdd =
      -(((((g : GL ι R) : Matrix ι ι R) i j))) :=
  upperUnitriangular_covBy_inv_entry g hij

theorem upperElementary_covBy_mul_entry
    (g h : upperElementarySubgroup ι R) {i j : ι} (hij : i ⋖ j) :
    (((((g * h : upperElementarySubgroup ι R) : GL ι R) :
        Matrix ι ι R) i j =
      ((((g : GL ι R) : Matrix ι ι R) i j +
        ((h : GL ι R) : Matrix ι ι R) i j)))) := by
  have hM : IsUpperTriangular ((((g : GL ι R) : Matrix ι ι R))) :=
    upperElementary_isUpperTriangular_commRing g
  have hN : IsUpperTriangular ((((h : GL ι R) : Matrix ι ι R))) :=
    upperElementary_isUpperTriangular_commRing h
  have hM_diag : ∀ k, ((((g : GL ι R) : Matrix ι ι R) k k = 1)) :=
    upperElementary_diag_one_commRing g
  have hN_diag : ∀ k, ((((h : GL ι R) : Matrix ι ι R) k k = 1)) :=
    upperElementary_diag_one_commRing h
  have hMulMat :
      ((((((g * h : upperElementarySubgroup ι R) : GL ι R) :
          Matrix ι ι R) =
        ((((g : GL ι R) : Matrix ι ι R) *
          ((h : GL ι R) : Matrix ι ι R)))))) := by simp
  rw [hMulMat]
  exact isUpperTriangular_covBy_mul_entry hM hN hM_diag hN_diag hij

theorem upperElementary_covBy_one_entry
    {i j : ι} (hij : i ⋖ j) :
    (((((1 : upperElementarySubgroup ι R) : GL ι R) :
        Matrix ι ι R) i j = 0)) := by
  have h1 : (((((1 : upperElementarySubgroup ι R) : GL ι R) :
      Matrix ι ι R) = (1 : Matrix ι ι R))) := by simp
  rw [h1]
  exact isUpperTriangular_covBy_one_entry hij

theorem upperElementary_covBy_inv_entry
    (g : upperElementarySubgroup ι R) {i j : ι} (hij : i ⋖ j) :
    (((((g⁻¹ : upperElementarySubgroup ι R) : GL ι R) :
        Matrix ι ι R) i j =
      -(((((g : GL ι R) : Matrix ι ι R) i j))))) := by
  have hM : IsUpperTriangular ((((g : GL ι R) : Matrix ι ι R))) :=
    upperElementary_isUpperTriangular_commRing g
  have hMi : ∀ k, ((((g : GL ι R) : Matrix ι ι R) k k = 1)) :=
    upperElementary_diag_one_commRing g
  have hMinv : IsUpperTriangular
      ((((((g⁻¹ : upperElementarySubgroup ι R) : GL ι R) :
          Matrix ι ι R)))) :=
    upperElementary_isUpperTriangular_commRing g⁻¹
  have hMinv_diag : ∀ k,
      ((((((g⁻¹ : upperElementarySubgroup ι R) : GL ι R) :
          Matrix ι ι R) k k = 1))) :=
    upperElementary_diag_one_commRing g⁻¹
  have hMul :
      ((((g : GL ι R) : Matrix ι ι R) *
        ((((g⁻¹ : upperElementarySubgroup ι R) : GL ι R) :
            Matrix ι ι R)) = 1)) := by
    have hGL : (g : GL ι R) *
        (((g⁻¹ : upperElementarySubgroup ι R) : GL ι R)) = 1 := by
      have h1 : (((g⁻¹ : upperElementarySubgroup ι R) : GL ι R)) =
          (g : GL ι R)⁻¹ := rfl
      rw [h1, mul_inv_cancel]
    calc ((((g : GL ι R) : Matrix ι ι R) *
        ((((g⁻¹ : upperElementarySubgroup ι R) : GL ι R) :
            Matrix ι ι R))))
        = (((((g : GL ι R) *
            (((g⁻¹ : upperElementarySubgroup ι R) : GL ι R) :
              GL ι R)).val : Matrix ι ι R))) := by simp
      _ = ((((1 : GL ι R).val : Matrix ι ι R))) := by rw [hGL]
      _ = 1 := by simp
  exact isUpperTriangular_covBy_inv_entry hM hMi hMinv hMinv_diag hMul hij

/-- Elementary subgroup version of the cover coefficient homomorphism. -/
def upperElementaryCoverCoeffHom
    (i j : ι) (hij : i ⋖ j) :
    upperElementarySubgroup ι R →* Multiplicative R where
  toFun g := Multiplicative.ofAdd (((((g : GL ι R) : Matrix ι ι R) i j)))
  map_one' := by
    have h0 := upperElementary_covBy_one_entry (R := R) hij
    calc Multiplicative.ofAdd
          (((((1 : upperElementarySubgroup ι R) : GL ι R) :
              Matrix ι ι R) i j))
        = Multiplicative.ofAdd (0 : R) := by rw [h0]
      _ = 1 := rfl
  map_mul' g h := by
    have hEq := upperElementary_covBy_mul_entry g h hij
    calc Multiplicative.ofAdd
          (((((g * h : upperElementarySubgroup ι R) : GL ι R) :
              Matrix ι ι R) i j))
        = Multiplicative.ofAdd
            (((((g : GL ι R) : Matrix ι ι R) i j +
              ((h : GL ι R) : Matrix ι ι R) i j))) := by rw [hEq]
      _ = Multiplicative.ofAdd (((((g : GL ι R) : Matrix ι ι R) i j))) *
          Multiplicative.ofAdd (((((h : GL ι R) : Matrix ι ι R) i j))) := rfl

@[simp]
theorem upperElementaryCoverCoeffHom_apply
    (i j : ι) (hij : i ⋖ j) (g : upperElementarySubgroup ι R) :
    (upperElementaryCoverCoeffHom (R := R) i j hij g).toAdd =
      (((((g : GL ι R) : Matrix ι ι R) i j))) := rfl

theorem upperElementaryCoverCoeffHom_inv
    (i j : ι) (hij : i ⋖ j) (g : upperElementarySubgroup ι R) :
    (upperElementaryCoverCoeffHom i j hij g⁻¹).toAdd =
      -((((((g : GL ι R) : Matrix ι ι R) i j)))) :=
  upperElementary_covBy_inv_entry g hij

theorem upperElementaryCoverCoeffHom_mapRingHom
    {S : Type*} [CommRing S] (f : R →+* S)
    (i j : ι) (hij : i ⋖ j) (g : upperElementarySubgroup ι R) :
    f ((upperElementaryCoverCoeffHom i j hij g).toAdd) =
      (upperElementaryCoverCoeffHom i j hij
        (UpperElementary.mapRingHom f g)).toAdd := by
  simp [UpperElementary.coe_mapRingHom, Matrix.map_apply]

end CoverProduct

section Extraction

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {R : Type*} [CommRing R]

theorem upperElementary_elementary_entry
    {i j : ι} (hij : i ⋖ j) (a : R) :
    ((((UpperElementary.elementary i j hij.lt a :
        upperElementarySubgroup ι R) : GL ι R) : Matrix ι ι R) i j = a) := by
  have hNe : i ≠ j := hij.ne
  have hCoe : ((((UpperElementary.elementary i j hij.lt a :
      upperElementarySubgroup ι R) : GL ι R) : Matrix ι ι R) =
      (1 + Matrix.single i j a : Matrix ι ι R)) := rfl
  rw [hCoe]
  simp [Matrix.add_apply, hNe]

theorem upperElementary_elementary_inv_entry
    {i j : ι} (hij : i ⋖ j) (a : R) :
    ((((UpperElementary.elementary i j hij.lt a :
        upperElementarySubgroup ι R)⁻¹ : upperElementarySubgroup ι R) :
        GL ι R) : Matrix ι ι R) i j = -a := by
  have hInv : (UpperElementary.elementary i j hij.lt a :
      upperElementarySubgroup ι R)⁻¹ =
      UpperElementary.elementary i j hij.lt (-a) := by
    apply Subtype.ext
    simp [UpperElementary.coe_elementary, Matrix.GeneralLinearGroup.elementary_inv]
  rw [hInv]
  exact upperElementary_elementary_entry hij (-a)

/-- Left residual after extracting the simple-root coefficient. -/
def upperElementaryLeftResidual
    (t : upperElementarySubgroup ι R) {i j : ι} (hij : i ⋖ j) :
    upperElementarySubgroup ι R :=
  UpperElementary.elementary i j hij.lt
      (-((((t : GL ι R) : Matrix ι ι R) i j))) * t

/-- Right residual after extracting the simple-root coefficient. -/
def upperElementaryRightResidual
    (t : upperElementarySubgroup ι R) {i j : ι} (hij : i ⋖ j) :
    upperElementarySubgroup ι R :=
  t * UpperElementary.elementary i j hij.lt
      (-((((t : GL ι R) : Matrix ι ι R) i j)))

theorem upperElementaryLeftResidual_zero
    (t : upperElementarySubgroup ι R) {i j : ι} (hij : i ⋖ j) :
    ((((upperElementaryLeftResidual t hij : upperElementarySubgroup ι R) :
        GL ι R) : Matrix ι ι R) i j = 0) := by
  unfold upperElementaryLeftResidual
  have hMul := upperElementary_covBy_mul_entry
    (UpperElementary.elementary i j hij.lt
      (-((((t : GL ι R) : Matrix ι ι R) i j))))
    t hij
  rw [hMul, upperElementary_elementary_entry hij
    (-((((t : GL ι R) : Matrix ι ι R) i j)))]
  abel

theorem upperElementaryRightResidual_zero
    (t : upperElementarySubgroup ι R) {i j : ι} (hij : i ⋖ j) :
    ((((upperElementaryRightResidual t hij : upperElementarySubgroup ι R) :
        GL ι R) : Matrix ι ι R) i j = 0) := by
  unfold upperElementaryRightResidual
  have hMul := upperElementary_covBy_mul_entry t
    (UpperElementary.elementary i j hij.lt
      (-((((t : GL ι R) : Matrix ι ι R) i j)))) hij
  rw [hMul, upperElementary_elementary_entry hij
    (-((((t : GL ι R) : Matrix ι ι R) i j)))]
  abel

theorem upperElementary_leftExtraction
    (t : upperElementarySubgroup ι R) {i j : ι} (hij : i ⋖ j) :
    t = UpperElementary.elementary i j hij.lt
        ((((t : GL ι R) : Matrix ι ι R) i j)) *
        upperElementaryLeftResidual t hij := by
  unfold upperElementaryLeftResidual
  have hOne : UpperElementary.elementary i j hij.lt
        ((((t : GL ι R) : Matrix ι ι R) i j)) *
      UpperElementary.elementary i j hij.lt
        (-((((t : GL ι R) : Matrix ι ι R) i j))) = 1 := by
    have hMul : UpperElementary.elementary i j hij.lt
          ((((t : GL ι R) : Matrix ι ι R) i j)) *
        UpperElementary.elementary i j hij.lt
          (-((((t : GL ι R) : Matrix ι ι R) i j))) =
        UpperElementary.elementary i j hij.lt 0 := by
      apply Subtype.ext
      simp [UpperElementary.coe_elementary,
        Matrix.GeneralLinearGroup.elementary_mul_same]
    rw [hMul]
    apply Subtype.ext
    simp [UpperElementary.coe_elementary]
  calc t = 1 * t := by simp
    _ = (UpperElementary.elementary i j hij.lt
          ((((t : GL ι R) : Matrix ι ι R) i j)) *
        UpperElementary.elementary i j hij.lt
          (-((((t : GL ι R) : Matrix ι ι R) i j))) * t) := by
          rw [hOne]
    _ = UpperElementary.elementary i j hij.lt
          ((((t : GL ι R) : Matrix ι ι R) i j)) *
        (UpperElementary.elementary i j hij.lt
            (-((((t : GL ι R) : Matrix ι ι R) i j))) * t) := by
          rw [mul_assoc]

theorem upperElementary_rightExtraction
    (t : upperElementarySubgroup ι R) {i j : ι} (hij : i ⋖ j) :
    t = upperElementaryRightResidual t hij *
        UpperElementary.elementary i j hij.lt
          ((((t : GL ι R) : Matrix ι ι R) i j)) := by
  unfold upperElementaryRightResidual
  have hOne : UpperElementary.elementary i j hij.lt
        (-((((t : GL ι R) : Matrix ι ι R) i j))) *
      UpperElementary.elementary i j hij.lt
        ((((t : GL ι R) : Matrix ι ι R) i j)) = 1 := by
    have hMul : UpperElementary.elementary i j hij.lt
          (-((((t : GL ι R) : Matrix ι ι R) i j))) *
        UpperElementary.elementary i j hij.lt
          ((((t : GL ι R) : Matrix ι ι R) i j)) =
        UpperElementary.elementary i j hij.lt 0 := by
      apply Subtype.ext
      simp [UpperElementary.coe_elementary,
        Matrix.GeneralLinearGroup.elementary_mul_same]
    rw [hMul]
    apply Subtype.ext
    simp [UpperElementary.coe_elementary]
  calc t = t * 1 := by simp
    _ = t * (UpperElementary.elementary i j hij.lt
          (-((((t : GL ι R) : Matrix ι ι R) i j))) *
        UpperElementary.elementary i j hij.lt
          ((((t : GL ι R) : Matrix ι ι R) i j))) := by
          rw [hOne]
    _ = t * UpperElementary.elementary i j hij.lt
          (-((((t : GL ι R) : Matrix ι ι R) i j))) *
        UpperElementary.elementary i j hij.lt
          ((((t : GL ι R) : Matrix ι ι R) i j)) := by
          rw [mul_assoc]

theorem upperElementary_leftCoeff_unique
    (t : upperElementarySubgroup ι R) {i j : ι} (hij : i ⋖ j)
    {a : R} {r : upperElementarySubgroup ι R}
    (hrZero : ((((r : GL ι R) : Matrix ι ι R) i j = 0)))
    (hEq : t = UpperElementary.elementary i j hij.lt a * r) :
    a = ((((t : GL ι R) : Matrix ι ι R) i j)) := by
  have hMul := upperElementary_covBy_mul_entry
    (UpperElementary.elementary i j hij.lt a) r hij
  have hElEntry := upperElementary_elementary_entry hij a
  have hTRw : ((((t : GL ι R) : Matrix ι ι R) i j) =
      a + ((((r : GL ι R) : Matrix ι ι R) i j))) := by
    rw [hEq, hMul, hElEntry]
  rw [hrZero, add_zero] at hTRw
  exact hTRw.symm

theorem upperElementary_rightCoeff_unique
    (t : upperElementarySubgroup ι R) {i j : ι} (hij : i ⋖ j)
    {a : R} {r : upperElementarySubgroup ι R}
    (hrZero : ((((r : GL ι R) : Matrix ι ι R) i j = 0)))
    (hEq : t = r * UpperElementary.elementary i j hij.lt a) :
    a = ((((t : GL ι R) : Matrix ι ι R) i j)) := by
  have hMul := upperElementary_covBy_mul_entry r
    (UpperElementary.elementary i j hij.lt a) hij
  have hElEntry := upperElementary_elementary_entry hij a
  have hTRw : ((((t : GL ι R) : Matrix ι ι R) i j) =
      ((((r : GL ι R) : Matrix ι ι R) i j) + a)) := by
    rw [hEq, hMul, hElEntry]
  rw [hrZero, zero_add] at hTRw
  exact hTRw.symm

theorem upperElementary_leftResidual_unique
    (t : upperElementarySubgroup ι R) {i j : ι} (hij : i ⋖ j)
    {a : R} {r : upperElementarySubgroup ι R}
    (hrZero : ((((r : GL ι R) : Matrix ι ι R) i j = 0)))
    (hEq : t = UpperElementary.elementary i j hij.lt a * r) :
    r = upperElementaryLeftResidual t hij := by
  have ha := upperElementary_leftCoeff_unique t hij hrZero hEq
  rw [ha] at hEq
  have hInv : (UpperElementary.elementary i j hij.lt
      ((((t : GL ι R) : Matrix ι ι R) i j)))⁻¹ =
      UpperElementary.elementary i j hij.lt
        (-((((t : GL ι R) : Matrix ι ι R) i j))) := by
    apply Subtype.ext
    simp [UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.elementary_inv]
  let b : upperElementarySubgroup ι R :=
    UpperElementary.elementary i j hij.lt
      ((((t : GL ι R) : Matrix ι ι R) i j))
  have h1 : r = b⁻¹ * (b * r) :=
    (inv_mul_cancel_left b r).symm
  calc r = b⁻¹ * (b * r) := h1
    _ = b⁻¹ * t := by rw [← hEq]
    _ = upperElementaryLeftResidual t hij := by
          simp [upperElementaryLeftResidual, hInv, b]

theorem upperElementary_rightResidual_unique
    (t : upperElementarySubgroup ι R) {i j : ι} (hij : i ⋖ j)
    {a : R} {r : upperElementarySubgroup ι R}
    (hrZero : ((((r : GL ι R) : Matrix ι ι R) i j = 0)))
    (hEq : t = r * UpperElementary.elementary i j hij.lt a) :
    r = upperElementaryRightResidual t hij := by
  have ha := upperElementary_rightCoeff_unique t hij hrZero hEq
  rw [ha] at hEq
  have hInv : (UpperElementary.elementary i j hij.lt
      ((((t : GL ι R) : Matrix ι ι R) i j)))⁻¹ =
      UpperElementary.elementary i j hij.lt
        (-((((t : GL ι R) : Matrix ι ι R) i j))) := by
    apply Subtype.ext
    simp [UpperElementary.coe_elementary,
      Matrix.GeneralLinearGroup.elementary_inv]
  let b : upperElementarySubgroup ι R :=
    UpperElementary.elementary i j hij.lt
      ((((t : GL ι R) : Matrix ι ι R) i j))
  calc r = r * (b * b⁻¹) := by simp [mul_inv_cancel]
    _ = (r * b) * b⁻¹ := by rw [mul_assoc]
    _ = t * b⁻¹ := by rw [← hEq]
    _ = upperElementaryRightResidual t hij := by
          simp [upperElementaryRightResidual, hInv, b]

theorem upperElementaryLeftResidual_of_zero
    (t : upperElementarySubgroup ι R) {i j : ι} (hij : i ⋖ j)
    (hZero : ((((t : GL ι R) : Matrix ι ι R) i j = 0))) :
    upperElementaryLeftResidual t hij = t := by
  unfold upperElementaryLeftResidual
  rw [hZero, neg_zero]
  have hElZero : UpperElementary.elementary i j hij.lt (0 : R) = 1 := by
    apply Subtype.ext
    simp [UpperElementary.coe_elementary]
  rw [hElZero]
  simp

theorem upperElementaryRightResidual_of_zero
    (t : upperElementarySubgroup ι R) {i j : ι} (hij : i ⋖ j)
    (hZero : ((((t : GL ι R) : Matrix ι ι R) i j = 0))) :
    upperElementaryRightResidual t hij = t := by
  unfold upperElementaryRightResidual
  rw [hZero, neg_zero]
  have hElZero : UpperElementary.elementary i j hij.lt (0 : R) = 1 := by
    apply Subtype.ext
    simp [UpperElementary.coe_elementary]
  rw [hElZero]
  simp

end Extraction
section MonomialConjugation

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : Type*} [CommRing R]
variable {S : Type*} [CommRing S]

open PermutationBilinearCocycle

theorem monomialMatrixHom_val_entry
    (x : MonomialBase Rˣ ι) (p q : ι) :
    (monomialMatrixHom R ι x).val p q =
      if x.right q = p then (x.left p : R) else 0 := by
  have hCoe : (monomialMatrixHom R ι x).val =
      Matrix.diagonal (fun i => (x.left i : R)) * (x.right⁻¹).permMatrix R := by
    rw [coe_monomialMatrixHom_mk]
  rw [hCoe, diag_mul_perm_eq]
  have hIff : (x.right⁻¹ p = q) ↔ (x.right q = p) := by
    constructor
    · intro h; have : x.right (x.right⁻¹ p) = p := Equiv.apply_symm_apply x.right p
      calc x.right q = x.right (x.right⁻¹ p) := by rw [h]
        _ = p := this
    · intro h; rw [Equiv.Perm.inv_eq_iff_eq]; exact h.symm
  by_cases h : x.right⁻¹ p = q
  · have h2 : x.right q = p := hIff.mp h
    rw [ite_eq_left h, ite_eq_left h2]
  · have h2 : ¬ x.right q = p := fun hh => h (hIff.mpr hh)
    rw [ite_eq_right h, ite_eq_right h2]

private theorem mul_single_entry_general (M : Matrix ι ι R) (i j : ι) (a : R) (p q : ι) :
    (M * Matrix.single i j a) p q = if q = j then M p i * a else 0 := by
  classical
  by_cases hq : q = j
  · have hSingle : ∀ k : ι, Matrix.single i j a k q = if k = i then a else (0 : R) := by
      intro k; simp [Matrix.single_apply, hq, eq_comm]
    have hEq : (M * Matrix.single i j a) p q = ∑ k : ι, M p k * (if k = i then a else (0 : R)) := by
      simp [Matrix.mul_apply, hSingle]
    rw [hEq, ite_eq_left hq]
    have h1 : ∀ k : ι, M p k * (if k = i then a else (0 : R)) =
        if k = i then M p k * a else (0 : R) := by
      intro k; by_cases hk : k = i <;> simp [hk]
    calc ∑ k : ι, M p k * (if k = i then a else (0 : R))
        = ∑ k : ι, if k = i then M p k * a else (0 : R) := by
          apply Finset.sum_congr rfl; intro k _; rw [h1 k]
      _ = M p i * a := by rw [Finset.sum_ite_eq' Finset.univ i]; simp
  · have hSingleZero : ∀ k : ι, Matrix.single i j a k q = (0 : R) := by
      intro k; have hjq : ¬ j = q := Ne.symm hq; simp [hjq]
    have hEq : (M * Matrix.single i j a) p q = ∑ k : ι, M p k * (0 : R) := by
      simp [Matrix.mul_apply, hSingleZero]
    rw [hEq, ite_eq_right hq]; simp

private theorem single_mul_entry_general (b : R) (i j : ι) (M : Matrix ι ι R) (p q : ι) :
    (Matrix.single i j b * M) p q = if p = i then b * M j q else 0 := by
  classical
  by_cases hp : p = i
  · have hSingle : ∀ k : ι, Matrix.single i j b p k = if k = j then b else (0 : R) := by
      intro k; simp [Matrix.single_apply, hp, eq_comm]
    have hEq : (Matrix.single i j b * M) p q = ∑ k : ι, (if k = j then b else (0 : R)) * M k q := by
      simp [Matrix.mul_apply, hSingle]
    rw [hEq, ite_eq_left hp]
    have h1 : ∀ k : ι, (if k = j then (b : R) else 0) * M k q =
        if k = j then b * M k q else (0 : R) := by
      intro k; by_cases hk : k = j <;> simp [hk]
    calc ∑ k : ι, (if k = j then (b : R) else 0) * M k q
        = ∑ k : ι, if k = j then b * M k q else (0 : R) := by
          apply Finset.sum_congr rfl; intro k _; rw [h1 k]
      _ = b * M j q := by rw [Finset.sum_ite_eq' Finset.univ j]; simp
  · have hSingleZero : ∀ k : ι, Matrix.single i j b p k = (0 : R) := by
      intro k; have hip : ¬ i = p := Ne.symm hp; simp [hip]
    have hEq : (Matrix.single i j b * M) p q = ∑ k : ι, (0 : R) * M k q := by
      simp [Matrix.mul_apply, hSingleZero]
    rw [hEq, ite_eq_right hp]; simp

theorem monomialMatrixHom_mul_single
    (x : MonomialBase Rˣ ι) (i j : ι) (a : R) :
    (monomialMatrixHom R ι x).val * Matrix.single i j a =
      Matrix.single (x.right i) (x.right j)
        ((x.left (x.right i) : R) * a * ((x.left (x.right j))⁻¹ : Rˣ).val) *
        (monomialMatrixHom R ι x).val := by
  ext p q
  rw [mul_single_entry_general, single_mul_entry_general]
  have hMon_pi : (monomialMatrixHom R ι x).val p i =
      if p = x.right i then (x.left (x.right i) : R) else 0 := by
    have h := monomialMatrixHom_val_entry (R := R) x p i
    by_cases hp : p = x.right i
    · simp [hp]
    · simp [hp, h, eq_comm]
  have hMon_jq : (monomialMatrixHom R ι x).val (x.right j) q =
      if q = j then (x.left (x.right j) : R) else 0 := by
    have h := monomialMatrixHom_val_entry (R := R) x (x.right j) q
    have hIff : x.right q = x.right j ↔ q = j := by
      constructor
      · intro hh; exact Equiv.injective x.right hh
      · intro hh; rw [hh]
    by_cases hq : q = j
    · simp [hq]
    · simp [hq, h, hIff]
  by_cases hp : p = x.right i
  · by_cases hq : q = j
    · have hEq : (if q = j then (monomialMatrixHom R ι x).val p i * a else (0 : R)) =
          ((x.left (x.right i) : R) * a) := by simp [hp, hq]
      have hEq2 :
          (if p = x.right i then
            ((x.left (x.right i) : R) * a *
              ((x.left (x.right j))⁻¹ : Rˣ).val) *
              (monomialMatrixHom R ι x).val (x.right j) q
            else (0 : R)) =
          (((x.left (x.right i) : R) * a *
            ((x.left (x.right j))⁻¹ : Rˣ).val) *
            (x.left (x.right j) : R)) := by
        simp [hp, hq]
      rw [hEq, hEq2]
      have hWj : (x.left (x.right j) : R) * ((x.left (x.right j))⁻¹ : Rˣ).val = 1 := by
        have h1 : ((x.left (x.right j) : Rˣ) * (x.left (x.right j))⁻¹ : Rˣ) = 1 := by simp
        have h2 : (((x.left (x.right j) * (x.left (x.right j))⁻¹ : Rˣ) : R) = 1) := by rw [h1]; rfl
        calc (x.left (x.right j) : R) * ((x.left (x.right j))⁻¹ : Rˣ).val
            = (((x.left (x.right j) * (x.left (x.right j))⁻¹ : Rˣ) : R)) := by
              rfl
          _ = 1 := h2
      calc (x.left (x.right i) : R) * a
          = (x.left (x.right i) : R) * a * 1 := by simp
        _ = (x.left (x.right i) : R) * a *
            ((x.left (x.right j) : R) * ((x.left (x.right j))⁻¹ : Rˣ).val) := by rw [hWj]
        _ = ((x.left (x.right i) : R) * a * ((x.left (x.right j))⁻¹ : Rˣ).val) *
            (x.left (x.right j) : R) := by
            simp [mul_assoc, mul_comm, mul_left_comm]
    · simp [hp, hq, hMon_jq]
  · by_cases hq : q = j
    · simp [hp, hq, hMon_pi]
    · simp [hp, hq]

theorem monomialMatrixHom_conj_elementary
    (x : MonomialBase Rˣ ι) (i j : ι) (hij : i ≠ j) (a : R) :
    monomialMatrixHom R ι x * Matrix.GeneralLinearGroup.elementary i j hij a *
      (monomialMatrixHom R ι x)⁻¹ =
      Matrix.GeneralLinearGroup.elementary (x.right i) (x.right j)
        (fun h => hij (Equiv.injective x.right h))
        (((x.left (x.right i) : R) * a * ((x.left (x.right j))⁻¹ : Rˣ).val)) := by
  apply Units.ext
  have hMul := monomialMatrixHom_mul_single (R := R) x i j a
  have hAdd : (monomialMatrixHom R ι x).val * (1 + Matrix.single i j a) =
      (1 + Matrix.single (x.right i) (x.right j)
          (((x.left (x.right i) : R) * a * ((x.left (x.right j))⁻¹ : Rˣ).val))) *
        (monomialMatrixHom R ι x).val := by
    calc (monomialMatrixHom R ι x).val * (1 + Matrix.single i j a)
        = (monomialMatrixHom R ι x).val * 1 +
          (monomialMatrixHom R ι x).val * Matrix.single i j a := by rw [Matrix.mul_add]
      _ = (monomialMatrixHom R ι x).val +
          (monomialMatrixHom R ι x).val * Matrix.single i j a := by rw [Matrix.mul_one]
      _ = (monomialMatrixHom R ι x).val +
          Matrix.single (x.right i) (x.right j)
            (((x.left (x.right i) : R) * a * ((x.left (x.right j))⁻¹ : Rˣ).val)) *
            (monomialMatrixHom R ι x).val := by rw [hMul]
      _ = (1 + Matrix.single (x.right i) (x.right j)
            (((x.left (x.right i) : R) * a * ((x.left (x.right j))⁻¹ : Rˣ).val))) *
          (monomialMatrixHom R ι x).val := by
        simp [Matrix.add_mul]
  calc ((monomialMatrixHom R ι x * Matrix.GeneralLinearGroup.elementary i j hij a *
      (monomialMatrixHom R ι x)⁻¹ : GL ι R).val)
      = (monomialMatrixHom R ι x).val *
          ((Matrix.GeneralLinearGroup.elementary i j hij a : GL ι R).val) *
            ((monomialMatrixHom R ι x)⁻¹ : GL ι R).val := by simp [Units.val_mul]
    _ = (monomialMatrixHom R ι x).val * (1 + Matrix.single i j a) *
          ((monomialMatrixHom R ι x)⁻¹ : GL ι R).val := rfl
    _ = (1 + Matrix.single (x.right i) (x.right j)
            (((x.left (x.right i) : R) * a * ((x.left (x.right j))⁻¹ : Rˣ).val))) *
          (monomialMatrixHom R ι x).val *
            ((monomialMatrixHom R ι x)⁻¹ : GL ι R).val := by rw [hAdd]
    _ = (1 + Matrix.single (x.right i) (x.right j)
            (((x.left (x.right i) : R) * a * ((x.left (x.right j))⁻¹ : Rˣ).val))) *
          ((monomialMatrixHom R ι x * (monomialMatrixHom R ι x)⁻¹ : GL ι R).val) := by
        rw [Matrix.mul_assoc, ← Units.val_mul]
    _ = (1 + Matrix.single (x.right i) (x.right j)
            (((x.left (x.right i) : R) * a * ((x.left (x.right j))⁻¹ : Rˣ).val))) := by
        rw [mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = ((Matrix.GeneralLinearGroup.elementary (x.right i) (x.right j)
            (fun h => hij (Equiv.injective x.right h))
            (((x.left (x.right i) : R) * a *
              ((x.left (x.right j))⁻¹ : Rˣ).val)) : GL ι R).val) := rfl

theorem monomialMatrixHom_mul_elementary
    (x : MonomialBase Rˣ ι) (i j : ι) (hij : i ≠ j) (a : R) :
    monomialMatrixHom R ι x * Matrix.GeneralLinearGroup.elementary i j hij a =
      Matrix.GeneralLinearGroup.elementary (x.right i) (x.right j)
        (fun h => hij (Equiv.injective x.right h))
        (((x.left (x.right i) : R) * a * ((x.left (x.right j))⁻¹ : Rˣ).val)) *
        monomialMatrixHom R ι x := by
  have hConj := monomialMatrixHom_conj_elementary (R := R) x i j hij a
  calc monomialMatrixHom R ι x * Matrix.GeneralLinearGroup.elementary i j hij a
      = monomialMatrixHom R ι x * Matrix.GeneralLinearGroup.elementary i j hij a * 1 := by simp
    _ = monomialMatrixHom R ι x * Matrix.GeneralLinearGroup.elementary i j hij a *
          ((monomialMatrixHom R ι x)⁻¹ * monomialMatrixHom R ι x) := by rw [inv_mul_cancel]
    _ = (monomialMatrixHom R ι x * Matrix.GeneralLinearGroup.elementary i j hij a *
          (monomialMatrixHom R ι x)⁻¹) * monomialMatrixHom R ι x := by
        rw [← mul_assoc]
    _ = Matrix.GeneralLinearGroup.elementary (x.right i) (x.right j)
          (fun h => hij (Equiv.injective x.right h))
          (((x.left (x.right i) : R) * a * ((x.left (x.right j))⁻¹ : Rˣ).val)) *
        monomialMatrixHom R ι x := by rw [hConj]

theorem elementary_mul_monomialMatrixHom
    (x : MonomialBase Rˣ ι) (i j : ι) (hij : i ≠ j) (a : R) :
    Matrix.GeneralLinearGroup.elementary i j hij a * monomialMatrixHom R ι x =
      monomialMatrixHom R ι x *
        Matrix.GeneralLinearGroup.elementary ((Equiv.symm x.right i)) ((Equiv.symm x.right j))
          (fun h => hij (Equiv.injective (Equiv.symm x.right) h))
          ((((x.left i)⁻¹).val * a * (x.left j : R))) := by
  have hijSymm : (Equiv.symm x.right i) ≠ (Equiv.symm x.right j) :=
    fun h => hij (Equiv.injective (Equiv.symm x.right) h)
  have hMul := monomialMatrixHom_mul_elementary (R := R) x
      ((Equiv.symm x.right i)) ((Equiv.symm x.right j)) hijSymm
      ((((x.left i)⁻¹).val * a * (x.left j : R)))
  have hScaled : (x.left (x.right ((Equiv.symm x.right i))) : R) *
      ((((x.left i)⁻¹).val * a * (x.left j : R))) *
      ((x.left (x.right ((Equiv.symm x.right j))))⁻¹).val = a := by
    simp only [Equiv.apply_symm_apply]
    have h1 : (x.left i : R) * ((x.left i)⁻¹).val = 1 := by
      have : (x.left i * (x.left i)⁻¹ : Rˣ) = 1 := by simp
      have h := congrArg (fun u : Rˣ => (u : R)) this
      simp only [Units.val_mul] at h
      exact h
    have h2 : (x.left j : R) * ((x.left j)⁻¹).val = 1 := by
      have : (x.left j * (x.left j)⁻¹ : Rˣ) = 1 := by simp
      have h := congrArg (fun u : Rˣ => (u : R)) this
      simp only [Units.val_mul] at h
      exact h
    calc (x.left i : R) * ((((x.left i)⁻¹).val * a * (x.left j : R))) *
        ((x.left j)⁻¹).val
        = ((x.left i : R) * ((x.left i)⁻¹).val) * a *
          ((x.left j : R) * ((x.left j)⁻¹).val) := by
          simp only [mul_assoc, mul_comm, mul_left_comm]
      _ = 1 * a * 1 := by rw [h1, h2]
      _ = a := by simp
  have hEq : monomialMatrixHom R ι x *
      Matrix.GeneralLinearGroup.elementary ((Equiv.symm x.right i)) ((Equiv.symm x.right j))
        hijSymm ((((x.left i)⁻¹).val * a * (x.left j : R))) =
      Matrix.GeneralLinearGroup.elementary i j hij a *
        monomialMatrixHom R ι x := by
    calc monomialMatrixHom R ι x *
        Matrix.GeneralLinearGroup.elementary ((Equiv.symm x.right i)) ((Equiv.symm x.right j))
          hijSymm ((((x.left i)⁻¹).val * a * (x.left j : R)))
        = Matrix.GeneralLinearGroup.elementary (x.right ((Equiv.symm x.right i)))
            (x.right ((Equiv.symm x.right j)))
            (fun h => hijSymm (Equiv.injective x.right h))
            (((x.left (x.right ((Equiv.symm x.right i))) : R) *
              ((((x.left i)⁻¹).val * a * (x.left j : R))) *
              ((x.left (x.right ((Equiv.symm x.right j))))⁻¹).val)) *
          monomialMatrixHom R ι x := hMul
      _ = Matrix.GeneralLinearGroup.elementary i j hij a *
          monomialMatrixHom R ι x := by
        have hScaled' : (x.left i : R) * ((((x.left i)⁻¹).val * a * (x.left j : R))) *
            ((x.left j)⁻¹).val = a := by
          simpa [Equiv.apply_symm_apply] using hScaled
        have hElemEq : Matrix.GeneralLinearGroup.elementary
              (x.right ((Equiv.symm x.right) i)) (x.right ((Equiv.symm x.right) j))
              (fun h => hijSymm (Equiv.injective x.right h))
              (((x.left (x.right ((Equiv.symm x.right i))) : R) *
                ((((x.left i)⁻¹).val * a * (x.left j : R))) *
                ((x.left (x.right ((Equiv.symm x.right j))))⁻¹).val)) =
            Matrix.GeneralLinearGroup.elementary i j hij a := by
          apply Units.ext
          simp only [Matrix.GeneralLinearGroup.coe_elementary, Equiv.apply_symm_apply, hScaled']
        rw [hElemEq]
  exact hEq.symm

theorem monomialSLHom_conj_elementary
    (x : MonomialSL R ι) (i j : ι) (hij : i ≠ j) (a : R) :
    monomialSLHom R ι x * Matrix.SpecialLinearGroup.transvection hij a *
      (monomialSLHom R ι x)⁻¹ =
      Matrix.SpecialLinearGroup.transvection
        (fun h => hij (Equiv.injective x.1.right h))
        (((x.1.left (x.1.right i) : R) * a * ((x.1.left (x.1.right j))⁻¹ : Rˣ).val)) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  have hGL := monomialMatrixHom_conj_elementary (R := R) (x : MonomialBase Rˣ ι) i j hij a
  have hij' : x.1.right i ≠ x.1.right j := fun h => hij (Equiv.injective x.1.right h)
  have hToGL : Matrix.SpecialLinearGroup.toGL
      (monomialSLHom R ι x * Matrix.SpecialLinearGroup.transvection hij a *
        (monomialSLHom R ι x)⁻¹) =
      monomialMatrixHom R ι (x : MonomialBase Rˣ ι) *
        Matrix.GeneralLinearGroup.elementary i j hij a *
        (monomialMatrixHom R ι (x : MonomialBase Rˣ ι))⁻¹ := by
    calc Matrix.SpecialLinearGroup.toGL
          (monomialSLHom R ι x * Matrix.SpecialLinearGroup.transvection hij a *
            (monomialSLHom R ι x)⁻¹)
        = Matrix.SpecialLinearGroup.toGL (monomialSLHom R ι x) *
          Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij a) *
          Matrix.SpecialLinearGroup.toGL ((monomialSLHom R ι x)⁻¹) := by
          simp [map_mul]
      _ = Matrix.SpecialLinearGroup.toGL (monomialSLHom R ι x) *
          Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij a) *
          (Matrix.SpecialLinearGroup.toGL (monomialSLHom R ι x))⁻¹ := by
          rw [map_inv]
      _ = monomialMatrixHom R ι (x : MonomialBase Rˣ ι) *
          Matrix.GeneralLinearGroup.elementary i j hij a *
          (monomialMatrixHom R ι (x : MonomialBase Rˣ ι))⁻¹ := by
          have h1 : Matrix.SpecialLinearGroup.toGL (monomialSLHom R ι x) =
              monomialMatrixHom R ι (x : MonomialBase Rˣ ι) := by
            rw [monomialSLHom_toGL]
          have h2 : Matrix.SpecialLinearGroup.toGL
              (Matrix.SpecialLinearGroup.transvection hij a) =
              Matrix.GeneralLinearGroup.elementary i j hij a := by
            apply Units.ext
            simp [Matrix.SpecialLinearGroup.transvection_coe]
          rw [h1, h2]
  have hTransToGL : Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.transvection hij'
        (((x.1.left (x.1.right i) : R) * a * ((x.1.left (x.1.right j))⁻¹ : Rˣ).val))) =
      Matrix.GeneralLinearGroup.elementary (x.1.right i) (x.1.right j) hij'
        (((x.1.left (x.1.right i) : R) * a * ((x.1.left (x.1.right j))⁻¹ : Rˣ).val)) := by
    apply Units.ext
    simp [Matrix.SpecialLinearGroup.transvection_coe]
  rw [hToGL, hTransToGL, hGL]

omit [DecidableEq ι] [Fintype ι] in
theorem monomialMatrixHom_conj_elementary_mapRingHom
    (f : R →+* S) (x : MonomialBase Rˣ ι) (i j : ι) (_hij : i ≠ j) (a : R) :
    f (((x.left (x.right i) : R) * a * ((x.left (x.right j))⁻¹ : Rˣ).val)) =
      ((Units.map f.toMonoidHom (x.left (x.right i)) : Sˣ).val) * f a *
        (((Units.map f.toMonoidHom (x.left (x.right j)))⁻¹ : Sˣ).val) := by
  simp [Units.coe_map, Units.coe_map_inv, map_mul]

end MonomialConjugation

section OrderCriterion

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {R : Type*} [CommRing R]

open PermutationBilinearCocycle

theorem monomial_conj_elementary_mem_upperElementary_of_lt
    (x : MonomialBase Rˣ ι) {i j : ι} (hij : i ≠ j) (a : R)
    (hLt : x.right i < x.right j) :
    monomialMatrixHom R ι x * Matrix.GeneralLinearGroup.elementary i j hij a *
      (monomialMatrixHom R ι x)⁻¹ ∈ upperElementarySubgroup ι R := by
  rw [monomialMatrixHom_conj_elementary x i j hij a]
  exact elementary_mem_upperElementarySubgroup _ _ hLt _

theorem monomial_conj_elementary_mem_upperElementary_of_covBy
    (x : MonomialBase Rˣ ι) {i j : ι} (hij : i ⋖ j) (a : R)
    (hLt : x.right i < x.right j) :
    monomialMatrixHom R ι x *
        (UpperElementary.elementary i j hij.lt a : upperElementarySubgroup ι R).val *
      (monomialMatrixHom R ι x)⁻¹ ∈ upperElementarySubgroup ι R := by
  have hNe : i ≠ j := hij.ne
  have := monomial_conj_elementary_mem_upperElementary_of_lt (R := R) x hNe a hLt
  simpa [UpperElementary.coe_elementary] using this

end OrderCriterion

end GeneralLinearGroup

end Matrix
