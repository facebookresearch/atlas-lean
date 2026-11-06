/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitSpatialData

/-! The cleared coordinate matrices represent actual original Leech isometries. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Coordinate matrices multiply according to actual composition of Leech isometries. -/
theorem sixthFrameOrbit_isomMatrix_mul (a b : leechIsomSubgroup) :
    leechIsomMatrix (a * b) = leechIsomMatrix a * leechIsomMatrix b := by
  ext i j
  change a.val (b.val (Pi.single j 1)) i = _
  rw [← leechIsomMatrix_mulVec a]
  rfl

/-- Every original monomial physical numerator is its actual real coordinate matrix. -/
theorem sixthFrameOrbit_monomial_physical_matrix (k : Fin 16) :
    leechIsomMatrix (sixthFrameOrbitMonomialIsometry k) =
      (sixthFrameOrbitMonomialNumerator k).map (Int.castRingHom ℝ) := by
  ext i j
  change (sixthFrameOrbitMonomialIsometry k).val (Pi.single j 1) i = _
  rw [sixthFrameOrbit_monomial_apply]
  simp only [sixthFrameOrbitMonomialNumerator, Matrix.map_apply]
  by_cases h : sixthFrameOrbitSpatialInput k i = j
  · simp [h]
  · simp [h]

/-- The actual original three-bases operator is the exact cleared physical column matrix. -/
theorem sixthFrameOrbit_xi_physical_matrix :
    leechIsomMatrix co1XiIsometry = (1 / 2 : ℝ) •
      co1XiNumerator.map (Int.castRingHom ℝ) := by
  ext i j
  change (co1XiMatrix *ᵥ Pi.single j 1) i = (1 / 2 : ℝ) * (co1XiNumerator i j : ℝ)
  rw [Matrix.mulVec_single]
  simp only [MulOpposite.op_one, one_smul, Matrix.col_apply]
  change (((co1XiNumerator i j : ℚ) / 2 : ℚ) : ℝ) =
    (1 / 2 : ℝ) * (co1XiNumerator i j : ℝ)
  push_cast
  ring

/-- The cleared literal integer matrix is exactly thirty-two times the actual axis matrix. -/
theorem sixthFrameOrbit_axis_physical_matrix :
    (griessConwayEncode generatedSixthAxis).1 =
      (1 / 32 : ℝ) • sixthFrameOrbitAxisNumerator.map (Int.castRingHom ℝ) := by
  rw [generatedSixth_axis_matrix]
  ext i j
  simp only [generatedSixthAxisMatrix, generatedSixthMiddlePairValue,
    sixthFrameOrbitAxisNumerator, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  split_ifs <;> norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
