/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiMatrix

/-! The genuine Q-corrected three-bases generator fixes the entire original fifth axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The full genuine corrected Xi fixes the original axis in all three actual coordinate blocks. -/
theorem generatedFifth_xi_full_fixed :
    rhoLocal (localFiberIntoH generatedFifthXiCorrectedFiber) generatedFifthAxis =
      generatedFifthAxis := by
  apply Function.LeftInverse.injective griessConwayDecode_encode
  apply Prod.ext
  · rw [generatedFourth_local_matrix]
    change conwayMatrixAction co1XiIsometry (griessConwayEncode generatedFifthAxis).1 = _
    exact generatedFifth_xi_matrix_fixed
  · exact Prod.ext generatedFifth_xi_encoded_short_fixed generatedFifth_xi_encoded_tensor_fixed

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
