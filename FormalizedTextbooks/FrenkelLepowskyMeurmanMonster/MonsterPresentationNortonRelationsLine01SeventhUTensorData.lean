/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integer coordinates of the proposed next-U tensor, retaining its actual Leech action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SeventhForwardData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactTensorColumns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderMatrix

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- A finite tensor vector from the proposed spin packets and the actual Norton Leech factor. -/
noncomputable def monsterNortonLine01TensorSeventhUVector : GriessSpace :=
  (1 / (64 * Real.sqrt 2) : ℝ) • ∑ i : Fin 16,
    monsterNortonTensorRankOne
      (monsterNortonUFiber.val.2.val (Pi.single (Fin.castLE (by omega) i) 1))
        (nortonUIntegerEmbed (monsterNortonLine01SeventhForwardPacket i))

/-- The exact integer physical tensor numerator of the proposed next-U vector. -/
def monsterNortonLine01SeventhUTensorIntegerNumerator (n : Fin 4096) (j : Fin 24) : ℤ :=
  ∑ i : Fin 16, monsterNortonLine01SeventhForwardPacket i n *
    monsterNortonUNumerator1 j (Fin.castLE (by omega) i)

/-- Every physical column of the actual Norton Leech factor has denominator four. -/
theorem monsterNortonUPhysicalMatrix_basis (k i : Fin 24) :
    monsterNortonUFiber.val.2.val (Pi.single k 1) i =
      (1 / 4 : ℝ) * (monsterNortonUNumerator1 i k : ℝ) := by
  rw [monsterNortonUFiber_leech_matrix]
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, monsterNortonUMatrixQ,
    Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  change (((1 / 4 : ℚ) * (monsterNortonUNumerator1 i k : ℚ) : ℚ) : ℝ) = _
  push_cast
  rfl

/-- All coordinates of the proposed next-U tensor have their exact integer scale. -/
theorem monsterNortonLine01SeventhUTensorInteger_coordinates (n : Fin 4096) (j : Fin 24) :
    monsterNortonTensorProjection monsterNortonLine01TensorSeventhUVector
      (golayLabelCoefficients n) j =
        (1 / (256 * Real.sqrt 2) : ℝ) *
          (monsterNortonLine01SeventhUTensorIntegerNumerator n j : ℝ) := by
  rw [monsterNortonLine01TensorSeventhUVector, map_smul, map_sum]
  simp only [monsterNortonTensorProjection_rank_one, conwayTensorCoordinates_tmul,
    nortonUIntegerEmbed, nortonUIntegerLabel_coeff, monsterNortonUPhysicalMatrix_basis,
    monsterNortonLine01SeventhUTensorIntegerNumerator, Int.cast_sum, Int.cast_mul,
    Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
