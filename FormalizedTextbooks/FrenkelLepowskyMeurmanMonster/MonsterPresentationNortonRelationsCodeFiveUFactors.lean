/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveSpinGaussian
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactIntegralVector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderMatrix

/-! Actual sparse physical factors for the whole code-five tensor transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct Matrix
set_option backward.isDefEq.respectTransparency false

/-- Original tensor units are genuine products of spin and physical coordinate units. -/
theorem monsterNortonTensorUnit_product (t : SpinIndex) (i : Fin 24) :
    monsterNortonTensorUnit t i = monsterNortonTensorLift (conwayTensorCoordinates
      ((Pi.single t 1 : SpinSpace) ⊗ₜ[ℝ] (Pi.single i 1 : Fin 24 → ℝ))) := by
  unfold monsterNortonTensorUnit
  congr 1
  ext u j
  simp only [conwaySpinColumn, conwayTensorCoordinates_tmul, Pi.single_apply]
  by_cases h : j = i <;> simp [h]

/-- A complete product-indexed tensor packet is exactly its two sparse physical factors. -/
theorem monsterNortonSparseTensor_product {I J : Type*} [Fintype I] [Fintype J]
    (r : I → SpinIndex) (j : J → Fin 24) (c : I → ℝ) (d : J → ℝ) :
    (∑ p : I × J, (c p.1 * d p.2) • monsterNortonTensorUnit (r p.1) (j p.2)) =
      monsterNortonTensorLift (conwayTensorCoordinates
        ((∑ i : I, c i • (Pi.single (r i) 1 : SpinSpace)) ⊗ₜ[ℝ]
          (∑ k : J, d k • (Pi.single (j k) 1 : Fin 24 → ℝ)))) := by
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum,
    TensorProduct.smul_tmul_smul, map_smul]
  rw [Fintype.sum_prod_type]
  simp only [monsterNortonTensorUnit_product]
  exact Finset.sum_comm

/-- Scalar normalization preserves the complete product-indexed factorization. -/
theorem monsterNortonSparseTensor_normalized {I J : Type*} [Fintype I] [Fintype J]
    (r : I → SpinIndex) (j : J → Fin 24) (c : I → ℝ) (d : J → ℝ) (k : ℝ) :
    (∑ p : I × J, (c p.1 * d p.2 / k) • monsterNortonTensorUnit (r p.1) (j p.2)) =
      (1 / k) • monsterNortonTensorLift (conwayTensorCoordinates
        ((∑ i : I, c i • (Pi.single (r i) 1 : SpinSpace)) ⊗ₜ[ℝ]
          (∑ a : J, d a • (Pi.single (j a) 1 : Fin 24 → ℝ)))) := by
  rw [← monsterNortonSparseTensor_product, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [smul_smul]
  congr 1
  ring

/-- The original forward physical vector has exactly its eight displayed nonzero columns. -/
theorem monsterNortonCodeFiveForwardLeech_sparse :
    (∑ i : Fin 8, (monsterNortonCodeFiveForwardLeech
      (monsterNortonCodeFiveForwardColumns i) : ℝ) •
        (Pi.single (monsterNortonCodeFiveForwardColumns i) 1 : Fin 24 → ℝ)) =
      fun j => (monsterNortonCodeFiveForwardLeech j : ℝ) := by
  ext j
  have h : (∑ i : Fin 8, monsterNortonCodeFiveForwardLeech
      (monsterNortonCodeFiveForwardColumns i) *
        (Pi.single (monsterNortonCodeFiveForwardColumns i) 1 : Fin 24 → ℤ) j) =
      monsterNortonCodeFiveForwardLeech j := by revert j; decide +kernel
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero] using (show
      (∑ i : Fin 8, (monsterNortonCodeFiveForwardLeech
        (monsterNortonCodeFiveForwardColumns i) : ℝ) *
          (Pi.single (monsterNortonCodeFiveForwardColumns i) 1 : Fin 24 → ℝ) j) =
        (monsterNortonCodeFiveForwardLeech j : ℝ) by
          simp only [Pi.single_apply, mul_ite, mul_one, mul_zero] at h ⊢
          exact_mod_cast h)

/-- The original inverse physical vector has exactly its four displayed nonzero columns. -/
theorem monsterNortonCodeFiveInverseLeech_sparse :
    (∑ i : Fin 4, (monsterNortonCodeFiveInverseLeech
      (monsterNortonCodeFiveInverseColumns i) : ℝ) •
        (Pi.single (monsterNortonCodeFiveInverseColumns i) 1 : Fin 24 → ℝ)) =
      fun j => (monsterNortonCodeFiveInverseLeech j : ℝ) := by
  ext j
  have h : (∑ i : Fin 4, monsterNortonCodeFiveInverseLeech
      (monsterNortonCodeFiveInverseColumns i) *
        (Pi.single (monsterNortonCodeFiveInverseColumns i) 1 : Fin 24 → ℤ) j) =
      monsterNortonCodeFiveInverseLeech j := by revert j; decide +kernel
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero] using (show
      (∑ i : Fin 4, (monsterNortonCodeFiveInverseLeech
        (monsterNortonCodeFiveInverseColumns i) : ℝ) *
          (Pi.single (monsterNortonCodeFiveInverseColumns i) 1 : Fin 24 → ℝ) j) =
        (monsterNortonCodeFiveInverseLeech j : ℝ) by
          simp only [Pi.single_apply, mul_ite, mul_one, mul_zero] at h ⊢
          exact_mod_cast h)

/-- The actual seven-factor Norton spatial operator transports the complete physical vector. -/
theorem monsterNortonCodeFiveLeech_transport :
    monsterNortonUFiber.val.2.val (fun i => (monsterNortonCodeFiveForwardLeech i : ℝ)) =
      fun i => (monsterNortonCodeFiveInverseLeech i : ℝ) := by
  have hq : monsterNortonUMatrixQ *ᵥ (fun i => (monsterNortonCodeFiveForwardLeech i : ℚ)) =
      fun i => (monsterNortonCodeFiveInverseLeech i : ℚ) := by
    ext j
    change (∑ i : Fin 24, ((1 / 4 : ℚ) * (monsterNortonUNumerator1 j i : ℚ)) *
      (monsterNortonCodeFiveForwardLeech i : ℚ)) = _
    have hc : (∑ i : Fin 24, (monsterNortonUNumerator1 j i : ℚ) *
        (monsterNortonCodeFiveForwardLeech i : ℚ)) =
        4 * (monsterNortonCodeFiveInverseLeech j : ℚ) := by
      exact_mod_cast monsterNortonCodeFive_leech_certificate j
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hc]
    ring
  rw [monsterNortonUFiber_leech_matrix]
  ext j
  have h := congrArg (fun q : ℚ => (q : ℝ)) (congrFun hq j)
  simpa only [Matrix.mulVec, dotProduct, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast,
    Matrix.map_apply, Rat.coe_castHom] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
