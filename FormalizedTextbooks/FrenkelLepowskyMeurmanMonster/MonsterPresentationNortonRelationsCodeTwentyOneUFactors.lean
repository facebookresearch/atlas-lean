/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveUFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyOneSpinGaussian

/-! Actual physical factors for the original code-twentyone Norton tensor transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct Matrix
set_option backward.isDefEq.respectTransparency false

/-- The original forward physical vector has exactly its eight displayed nonzero columns. -/
theorem monsterNortonCodeTwentyOneForwardLeech_sparse :
    (∑ i : Fin 4, (monsterNortonCodeTwentyOneForwardLeech
      (monsterNortonCodeTwentyOneForwardColumns i) : ℝ) •
        (Pi.single (monsterNortonCodeTwentyOneForwardColumns i) 1 : Fin 24 → ℝ)) =
      fun j => (monsterNortonCodeTwentyOneForwardLeech j : ℝ) := by
  ext j
  have h : (∑ i : Fin 4, monsterNortonCodeTwentyOneForwardLeech
      (monsterNortonCodeTwentyOneForwardColumns i) *
        (Pi.single (monsterNortonCodeTwentyOneForwardColumns i) 1 : Fin 24 → ℤ) j) =
      monsterNortonCodeTwentyOneForwardLeech j := by revert j; decide +kernel
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero] using (show
      (∑ i : Fin 4, (monsterNortonCodeTwentyOneForwardLeech
        (monsterNortonCodeTwentyOneForwardColumns i) : ℝ) *
          (Pi.single (monsterNortonCodeTwentyOneForwardColumns i) 1 : Fin 24 → ℝ) j) =
        (monsterNortonCodeTwentyOneForwardLeech j : ℝ) by
          simp only [Pi.single_apply, mul_ite, mul_one, mul_zero] at h ⊢
          exact_mod_cast h)

/-- The original inverse physical vector has exactly its four displayed nonzero columns. -/
theorem monsterNortonCodeTwentyOneInverseLeech_sparse :
    (∑ i : Fin 4, (monsterNortonCodeTwentyOneInverseLeech
      (monsterNortonCodeTwentyOneInverseColumns i) : ℝ) •
        (Pi.single (monsterNortonCodeTwentyOneInverseColumns i) 1 : Fin 24 → ℝ)) =
      fun j => (monsterNortonCodeTwentyOneInverseLeech j : ℝ) := by
  ext j
  have h : (∑ i : Fin 4, monsterNortonCodeTwentyOneInverseLeech
      (monsterNortonCodeTwentyOneInverseColumns i) *
        (Pi.single (monsterNortonCodeTwentyOneInverseColumns i) 1 : Fin 24 → ℤ) j) =
      monsterNortonCodeTwentyOneInverseLeech j := by revert j; decide +kernel
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero] using (show
      (∑ i : Fin 4, (monsterNortonCodeTwentyOneInverseLeech
        (monsterNortonCodeTwentyOneInverseColumns i) : ℝ) *
          (Pi.single (monsterNortonCodeTwentyOneInverseColumns i) 1 : Fin 24 → ℝ) j) =
        (monsterNortonCodeTwentyOneInverseLeech j : ℝ) by
          simp only [Pi.single_apply, mul_ite, mul_one, mul_zero] at h ⊢
          exact_mod_cast h)

/-- The actual seven-factor Norton spatial operator transports the complete physical vector. -/
theorem monsterNortonCodeTwentyOneLeech_transport :
    monsterNortonUFiber.val.2.val (fun i => (monsterNortonCodeTwentyOneForwardLeech i : ℝ)) =
      fun i => (monsterNortonCodeTwentyOneInverseLeech i : ℝ) := by
  have hq : monsterNortonUMatrixQ *ᵥ (fun i => (monsterNortonCodeTwentyOneForwardLeech i : ℚ)) =
      fun i => (monsterNortonCodeTwentyOneInverseLeech i : ℚ) := by
    ext j
    change (∑ i : Fin 24, ((1 / 4 : ℚ) * (monsterNortonUNumerator1 j i : ℚ)) *
      (monsterNortonCodeTwentyOneForwardLeech i : ℚ)) = _
    have hc : (∑ i : Fin 24, (monsterNortonUNumerator1 j i : ℚ) *
        (monsterNortonCodeTwentyOneForwardLeech i : ℚ)) =
        4 * (monsterNortonCodeTwentyOneInverseLeech j : ℚ) := by
      exact_mod_cast monsterNortonCodeTwentyOne_leech_certificate j
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hc]
    ring
  rw [monsterNortonUFiber_leech_matrix]
  ext j
  have h := congrArg (fun q : ℚ => (q : ℝ)) (congrFun hq j)
  simpa only [Matrix.mulVec, dotProduct, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast,
    Matrix.map_apply, Rat.coe_castHom] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
