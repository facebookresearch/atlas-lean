/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveUFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentySpinGaussian

/-! Actual physical factors for the original code-twenty Norton tensor transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct Matrix
set_option backward.isDefEq.respectTransparency false

/-- The original forward physical vector has exactly its eight displayed nonzero columns. -/
theorem monsterNortonCodeTwentyForwardLeech_sparse :
    (∑ i : Fin 4, (monsterNortonCodeTwentyForwardLeech
      (monsterNortonCodeTwentyForwardColumns i) : ℝ) •
        (Pi.single (monsterNortonCodeTwentyForwardColumns i) 1 : Fin 24 → ℝ)) =
      fun j => (monsterNortonCodeTwentyForwardLeech j : ℝ) := by
  ext j
  have h : (∑ i : Fin 4, monsterNortonCodeTwentyForwardLeech
      (monsterNortonCodeTwentyForwardColumns i) *
        (Pi.single (monsterNortonCodeTwentyForwardColumns i) 1 : Fin 24 → ℤ) j) =
      monsterNortonCodeTwentyForwardLeech j := by revert j; decide +kernel
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero] using (show
      (∑ i : Fin 4, (monsterNortonCodeTwentyForwardLeech
        (monsterNortonCodeTwentyForwardColumns i) : ℝ) *
          (Pi.single (monsterNortonCodeTwentyForwardColumns i) 1 : Fin 24 → ℝ) j) =
        (monsterNortonCodeTwentyForwardLeech j : ℝ) by
          simp only [Pi.single_apply, mul_ite, mul_one, mul_zero] at h ⊢
          exact_mod_cast h)

/-- The original inverse physical vector has exactly its four displayed nonzero columns. -/
theorem monsterNortonCodeTwentyInverseLeech_sparse :
    (∑ i : Fin 4, (monsterNortonCodeTwentyInverseLeech
      (monsterNortonCodeTwentyInverseColumns i) : ℝ) •
        (Pi.single (monsterNortonCodeTwentyInverseColumns i) 1 : Fin 24 → ℝ)) =
      fun j => (monsterNortonCodeTwentyInverseLeech j : ℝ) := by
  ext j
  have h : (∑ i : Fin 4, monsterNortonCodeTwentyInverseLeech
      (monsterNortonCodeTwentyInverseColumns i) *
        (Pi.single (monsterNortonCodeTwentyInverseColumns i) 1 : Fin 24 → ℤ) j) =
      monsterNortonCodeTwentyInverseLeech j := by revert j; decide +kernel
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero] using (show
      (∑ i : Fin 4, (monsterNortonCodeTwentyInverseLeech
        (monsterNortonCodeTwentyInverseColumns i) : ℝ) *
          (Pi.single (monsterNortonCodeTwentyInverseColumns i) 1 : Fin 24 → ℝ) j) =
        (monsterNortonCodeTwentyInverseLeech j : ℝ) by
          simp only [Pi.single_apply, mul_ite, mul_one, mul_zero] at h ⊢
          exact_mod_cast h)

/-- The actual seven-factor Norton spatial operator transports the complete physical vector. -/
theorem monsterNortonCodeTwentyLeech_transport :
    monsterNortonUFiber.val.2.val (fun i => (monsterNortonCodeTwentyForwardLeech i : ℝ)) =
      fun i => (monsterNortonCodeTwentyInverseLeech i : ℝ) := by
  have hq : monsterNortonUMatrixQ *ᵥ (fun i => (monsterNortonCodeTwentyForwardLeech i : ℚ)) =
      fun i => (monsterNortonCodeTwentyInverseLeech i : ℚ) := by
    ext j
    change (∑ i : Fin 24, ((1 / 4 : ℚ) * (monsterNortonUNumerator1 j i : ℚ)) *
      (monsterNortonCodeTwentyForwardLeech i : ℚ)) = _
    have hc : (∑ i : Fin 24, (monsterNortonUNumerator1 j i : ℚ) *
        (monsterNortonCodeTwentyForwardLeech i : ℚ)) =
        4 * (monsterNortonCodeTwentyInverseLeech j : ℚ) := by
      exact_mod_cast monsterNortonCodeTwenty_leech_certificate j
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hc]
    ring
  rw [monsterNortonUFiber_leech_matrix]
  ext j
  have h := congrArg (fun q : ℚ => (q : ℝ)) (congrFun hq j)
  simpa only [Matrix.mulVec, dotProduct, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast,
    Matrix.map_apply, Rat.coe_castHom] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
