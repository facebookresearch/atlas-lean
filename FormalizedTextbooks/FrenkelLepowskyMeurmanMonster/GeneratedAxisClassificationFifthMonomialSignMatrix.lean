/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMatrix

/-! Every original Golay sign lift and every correcting Q fix the actual fifth matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The physical Golay sign action fixes the entire actual diagonal fifth watermark. -/
theorem generatedFifth_sign_spatial_matrix (a : Fin 4096) :
    conwayMatrixAction (golaySignIsometry (sourceGeneratedSignCode a))
      (griessConwayEncode generatedFifthAxis).1 = (griessConwayEncode generatedFifthAxis).1 := by
  ext i j
  rw [sourceGeneratedSign_matrix_apply]
  by_cases hij : i = j
  · subst j
    rw [CharTwo.add_self_eq_zero, qSign_zero, one_mul]
  · rw [generatedFifth_matrix_off_diagonal i j hij, mul_zero]

/-- The chosen actual source sign word fixes the original matrix block. -/
theorem generatedFifth_sign_local_matrix (a : Fin 4096) (ε : ZMod 2) :
    (griessConwayEncode (rhoLocal (generatedFifthSignLocal a ε) generatedFifthAxis)).1 =
      (griessConwayEncode generatedFifthAxis).1 := by
  rw [generatedFifth_sign_local_action, sourceGeneratedY_matrix,
    generatedFifth_sign_spatial_matrix]

/-- Every actual Q correction preserves the matrix fixation of an original source sign lift. -/
theorem generatedFifth_sign_corrected_matrix (a : Fin 4096) (ε : ZMod 2) (q : Q) :
    (griessConwayEncode (rhoLocal
      (localFiberIntoH (localFiberIncl q * generatedFifthSignFiber a ε)) generatedFifthAxis)).1 =
        (griessConwayEncode generatedFifthAxis).1 := by
  rw [map_mul, generatedFifth_sign_fiber_local, map_mul]
  change (griessConwayEncode (rhoLocal (localFiberIntoH (localFiberIncl q))
    (rhoLocal (generatedFifthSignLocal a ε) generatedFifthAxis))).1 = _
  rw [generatedFourth_local_matrix]
  change conwayMatrixAction 1 _ = _
  rw [map_one]
  exact generatedFifth_sign_local_matrix a ε

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
