/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineTensorReindex

/-! The actual fourth generated-group axis has the exactly verified packed affine tensor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The original physical tensor of the literal fourth axis is exactly the packed affine tensor. -/
theorem generatedFourthQAffineTensor_actual :
    (griessConwayEncode generatedFourthAxis).2.2 = generatedFourthQAffineTensorPacked := by
  rw [generatedFourth_tensor_sum, generatedFourthQAffineTensor_signed_sum]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
