/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorInputData

/-! Every cached integer in this interval is checked against the true original tensor formula. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 64000000 in
-- Original signed coefficients are checked, including both spin halves and all physical columns.
/-- All candidate tensor integers in this interval have their complete true signed value. -/
theorem generatedSixth_xi_tensor_input_check02 : ∀ a : Fin 256, ∀ i : Fin 24,
    let n : Fin 4096 := ⟨2 * 256 + a.val, by omega⟩
    generatedSixthXiTensorInput n i = generatedSixthTensorFastExecutable n i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
