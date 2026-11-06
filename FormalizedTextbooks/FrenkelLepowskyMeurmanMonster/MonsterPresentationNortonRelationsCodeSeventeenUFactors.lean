/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveUFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeSeventeenSpinGaussian

/-! Actual physical factors for the original code-seventeen Norton tensor transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct Matrix
set_option backward.isDefEq.respectTransparency false

/-- The original forward physical vector has exactly its eight displayed nonzero columns. -/
theorem monsterNortonCodeSeventeenForwardLeech_sparse :
    (∑ i : Fin 4, (monsterNortonCodeSeventeenForwardLeech
      (monsterNortonCodeSeventeenForwardColumns i) : ℝ) •
        (Pi.single (monsterNortonCodeSeventeenForwardColumns i) 1 : Fin 24 → ℝ)) =
      fun j => (monsterNortonCodeSeventeenForwardLeech j : ℝ) := by
  ext j
  have h : (∑ i : Fin 4, monsterNortonCodeSeventeenForwardLeech
      (monsterNortonCodeSeventeenForwardColumns i) *
        (Pi.single (monsterNortonCodeSeventeenForwardColumns i) 1 : Fin 24 → ℤ) j) =
      monsterNortonCodeSeventeenForwardLeech j := by revert j; decide +kernel
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero] using (show
      (∑ i : Fin 4, (monsterNortonCodeSeventeenForwardLeech
        (monsterNortonCodeSeventeenForwardColumns i) : ℝ) *
          (Pi.single (monsterNortonCodeSeventeenForwardColumns i) 1 : Fin 24 → ℝ) j) =
        (monsterNortonCodeSeventeenForwardLeech j : ℝ) by
          simp only [Pi.single_apply, mul_ite, mul_one, mul_zero] at h ⊢
          exact_mod_cast h)

/-- The original inverse physical vector has exactly its four displayed nonzero columns. -/
theorem monsterNortonCodeSeventeenInverseLeech_sparse :
    (∑ i : Fin 4, (monsterNortonCodeSeventeenInverseLeech
      (monsterNortonCodeSeventeenInverseColumns i) : ℝ) •
        (Pi.single (monsterNortonCodeSeventeenInverseColumns i) 1 : Fin 24 → ℝ)) =
      fun j => (monsterNortonCodeSeventeenInverseLeech j : ℝ) := by
  ext j
  have h : (∑ i : Fin 4, monsterNortonCodeSeventeenInverseLeech
      (monsterNortonCodeSeventeenInverseColumns i) *
        (Pi.single (monsterNortonCodeSeventeenInverseColumns i) 1 : Fin 24 → ℤ) j) =
      monsterNortonCodeSeventeenInverseLeech j := by revert j; decide +kernel
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero] using (show
      (∑ i : Fin 4, (monsterNortonCodeSeventeenInverseLeech
        (monsterNortonCodeSeventeenInverseColumns i) : ℝ) *
          (Pi.single (monsterNortonCodeSeventeenInverseColumns i) 1 : Fin 24 → ℝ) j) =
        (monsterNortonCodeSeventeenInverseLeech j : ℝ) by
          simp only [Pi.single_apply, mul_ite, mul_one, mul_zero] at h ⊢
          exact_mod_cast h)

/-- The actual seven-factor Norton spatial operator transports the complete physical vector. -/
theorem monsterNortonCodeSeventeenLeech_transport :
    monsterNortonUFiber.val.2.val (fun i => (monsterNortonCodeSeventeenForwardLeech i : ℝ)) =
      fun i => (monsterNortonCodeSeventeenInverseLeech i : ℝ) := by
  have hq : monsterNortonUMatrixQ *ᵥ (fun i => (monsterNortonCodeSeventeenForwardLeech i : ℚ)) =
      fun i => (monsterNortonCodeSeventeenInverseLeech i : ℚ) := by
    ext j
    change (∑ i : Fin 24, ((1 / 4 : ℚ) * (monsterNortonUNumerator1 j i : ℚ)) *
      (monsterNortonCodeSeventeenForwardLeech i : ℚ)) = _
    have hc : (∑ i : Fin 24, (monsterNortonUNumerator1 j i : ℚ) *
        (monsterNortonCodeSeventeenForwardLeech i : ℚ)) =
        4 * (monsterNortonCodeSeventeenInverseLeech j : ℚ) := by
      exact_mod_cast monsterNortonCodeSeventeen_leech_certificate j
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hc]
    ring
  rw [monsterNortonUFiber_leech_matrix]
  ext j
  have h := congrArg (fun q : ℚ => (q : ℝ)) (congrFun hq j)
  simpa only [Matrix.mulVec, dotProduct, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast,
    Matrix.map_apply, Rat.coe_castHom] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
