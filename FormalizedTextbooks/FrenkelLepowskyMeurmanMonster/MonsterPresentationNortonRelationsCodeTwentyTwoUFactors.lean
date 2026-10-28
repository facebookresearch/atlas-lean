/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoMixedCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeFiveUFactors

/-! Complete actual physical transport for every basis22 tensor row. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators TensorProduct Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The entire integer physical row at one original spin label. -/
def monsterNortonCodeTwentyTwoLeechRowInteger (s : Fin 64) (j : Fin 24) : ℤ :=
  ∑ i : Fin 16, monsterNortonCodeTwentyTwoForwardTensorTable s i *
    (Pi.single (monsterNortonCodeTwentyTwoForwardColumns i) 1 : Fin 24 → ℤ) j

/-- Its whole original-coordinate real physical vector. -/
def monsterNortonCodeTwentyTwoLeechRow (s : Fin 64) : Fin 24 → ℝ :=
  fun j => (monsterNortonCodeTwentyTwoLeechRowInteger s j : ℝ)

/-- Every source physical row is exactly its sixteen displayed columns. -/
theorem monsterNortonCodeTwentyTwoLeechRow_sparse (s : Fin 64) :
    (∑ i : Fin 16, (monsterNortonCodeTwentyTwoForwardTensorTable s i : ℝ) •
      (Pi.single (monsterNortonCodeTwentyTwoForwardColumns i) 1 : Fin 24 → ℝ)) =
        monsterNortonCodeTwentyTwoLeechRow s := by
  ext j
  simp only [monsterNortonCodeTwentyTwoLeechRow, monsterNortonCodeTwentyTwoLeechRowInteger,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul,
    Pi.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero]

set_option maxHeartbeats 48000000 in
-- Check all sixty-four full rows against the actual twenty-four-coordinate source matrix.
/-- All full actual spatial rows produce the listed pre-spin coefficients and no other columns. -/
theorem monsterNortonCodeTwentyTwoLeechRow_certificate (s : Fin 64) (j : Fin 24) :
    (∑ i : Fin 24, monsterNortonUNumerator1 j i *
      monsterNortonCodeTwentyTwoLeechRowInteger s i) =
        4 * ∑ k : Fin 16, monsterNortonCodeTwentyTwoPreSpinColumnCoefficient k s *
          (Pi.single (monsterNortonCodeTwentyTwoInverseColumns k) 1 : Fin 24 → ℤ) j := by
  revert s j
  decide +kernel

/-- The actual seven-factor spatial operator transports the whole physical row. -/
theorem monsterNortonCodeTwentyTwoLeechRow_transport (s : Fin 64) :
    monsterNortonUFiber.val.2.val (monsterNortonCodeTwentyTwoLeechRow s) =
      ∑ k : Fin 16, (monsterNortonCodeTwentyTwoPreSpinColumnCoefficient k s : ℝ) •
        (Pi.single (monsterNortonCodeTwentyTwoInverseColumns k) 1 : Fin 24 → ℝ) := by
  have hq : monsterNortonUMatrixQ *ᵥ
      (fun i => (monsterNortonCodeTwentyTwoLeechRowInteger s i : ℚ)) =
        fun j => ∑ k : Fin 16, (monsterNortonCodeTwentyTwoPreSpinColumnCoefficient k s : ℚ) *
          (Pi.single (monsterNortonCodeTwentyTwoInverseColumns k) 1 : Fin 24 → ℚ) j := by
    ext j
    change (∑ i : Fin 24, ((1 / 4 : ℚ) * (monsterNortonUNumerator1 j i : ℚ)) *
      (monsterNortonCodeTwentyTwoLeechRowInteger s i : ℚ)) = _
    have hc : (∑ i : Fin 24, (monsterNortonUNumerator1 j i : ℚ) *
        (monsterNortonCodeTwentyTwoLeechRowInteger s i : ℚ)) =
          4 * ∑ k : Fin 16, (monsterNortonCodeTwentyTwoPreSpinColumnCoefficient k s : ℚ) *
            (Pi.single (monsterNortonCodeTwentyTwoInverseColumns k) 1 : Fin 24 → ℚ) j := by
      have h := monsterNortonCodeTwentyTwoLeechRow_certificate s j
      simp only [Pi.single_apply] at h ⊢
      exact_mod_cast h
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hc]
    ring
  rw [monsterNortonUFiber_leech_matrix]
  ext j
  have h := congrArg (fun q : ℚ => (q : ℝ)) (congrFun hq j)
  simpa only [monsterNortonCodeTwentyTwoLeechRow, Matrix.mulVec, dotProduct,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Matrix.map_apply, Rat.coe_castHom,
    Pi.single_apply, apply_ite, Rat.cast_one, Rat.cast_zero,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
