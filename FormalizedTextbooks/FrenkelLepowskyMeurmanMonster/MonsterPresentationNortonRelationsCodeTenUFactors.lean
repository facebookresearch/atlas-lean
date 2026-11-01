/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveUFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTenSpinGaussian

/-! Actual physical factors for the original basis-ten Norton tensor transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct Matrix
set_option backward.isDefEq.respectTransparency false

/-- The original forward physical vector has exactly its eight displayed nonzero columns. -/
theorem monsterNortonCodeTenForwardLeech_sparse :
    (∑ i : Fin 8, (monsterNortonCodeTenForwardLeech
      (monsterNortonCodeTenForwardColumns i) : ℝ) •
        (Pi.single (monsterNortonCodeTenForwardColumns i) 1 : Fin 24 → ℝ)) =
      fun j => (monsterNortonCodeTenForwardLeech j : ℝ) := by
  ext j
  have h : (∑ i : Fin 8, monsterNortonCodeTenForwardLeech
      (monsterNortonCodeTenForwardColumns i) *
        (Pi.single (monsterNortonCodeTenForwardColumns i) 1 : Fin 24 → ℤ) j) =
      monsterNortonCodeTenForwardLeech j := by revert j; decide +kernel
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero] using (show
      (∑ i : Fin 8, (monsterNortonCodeTenForwardLeech
        (monsterNortonCodeTenForwardColumns i) : ℝ) *
          (Pi.single (monsterNortonCodeTenForwardColumns i) 1 : Fin 24 → ℝ) j) =
        (monsterNortonCodeTenForwardLeech j : ℝ) by
          simp only [Pi.single_apply, mul_ite, mul_one, mul_zero] at h ⊢
          exact_mod_cast h)

/-- The original inverse physical vector has exactly its one displayed nonzero columns. -/
theorem monsterNortonCodeTenInverseLeech_sparse :
    (∑ i : Fin 1, (monsterNortonCodeTenInverseLeech
      (monsterNortonCodeTenInverseColumns i) : ℝ) •
        (Pi.single (monsterNortonCodeTenInverseColumns i) 1 : Fin 24 → ℝ)) =
      fun j => (monsterNortonCodeTenInverseLeech j : ℝ) := by
  ext j
  have h : (∑ i : Fin 1, monsterNortonCodeTenInverseLeech
      (monsterNortonCodeTenInverseColumns i) *
        (Pi.single (monsterNortonCodeTenInverseColumns i) 1 : Fin 24 → ℤ) j) =
      monsterNortonCodeTenInverseLeech j := by revert j; decide +kernel
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero] using (show
      (∑ i : Fin 1, (monsterNortonCodeTenInverseLeech
        (monsterNortonCodeTenInverseColumns i) : ℝ) *
          (Pi.single (monsterNortonCodeTenInverseColumns i) 1 : Fin 24 → ℝ) j) =
        (monsterNortonCodeTenInverseLeech j : ℝ) by
          simp only [Pi.single_apply, mul_ite, mul_one, mul_zero] at h ⊢
          exact_mod_cast h)

/-- The actual seven-factor Norton spatial operator transports the complete physical vector. -/
theorem monsterNortonCodeTenLeech_transport :
    monsterNortonUFiber.val.2.val (fun i => (monsterNortonCodeTenForwardLeech i : ℝ)) =
      fun i => (monsterNortonCodeTenInverseLeech i : ℝ) := by
  have hq : monsterNortonUMatrixQ *ᵥ (fun i => (monsterNortonCodeTenForwardLeech i : ℚ)) =
      fun i => (monsterNortonCodeTenInverseLeech i : ℚ) := by
    ext j
    change (∑ i : Fin 24, ((1 / 4 : ℚ) * (monsterNortonUNumerator1 j i : ℚ)) *
      (monsterNortonCodeTenForwardLeech i : ℚ)) = _
    have hc : (∑ i : Fin 24, (monsterNortonUNumerator1 j i : ℚ) *
        (monsterNortonCodeTenForwardLeech i : ℚ)) =
        4 * (monsterNortonCodeTenInverseLeech j : ℚ) := by
      exact_mod_cast monsterNortonCodeTen_leech_certificate j
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hc]
    ring
  rw [monsterNortonUFiber_leech_matrix]
  ext j
  have h := congrArg (fun q : ℚ => (q : ℝ)) (congrFun hq j)
  simpa only [Matrix.mulVec, dotProduct, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast,
    Matrix.map_apply, Rat.coe_castHom] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
