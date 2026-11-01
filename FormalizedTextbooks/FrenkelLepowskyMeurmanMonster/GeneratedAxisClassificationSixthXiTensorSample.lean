/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiSparseTensor

/-! A full original tensor row checks the exact conjugated-Xi numerator and normalization. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 8000000 in
-- Check every physical column and all original Gaussian terms at the first spin address.
/-- The original corrected Xi has the expected cleared numerator on the entire first tensor row. -/
theorem generatedSixth_xi_tensor_sample : ∀ i : Fin 24,
    generatedSixthXiSparseTensor 0 i = 16 * generatedSixthTensorExecutable 0 i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
