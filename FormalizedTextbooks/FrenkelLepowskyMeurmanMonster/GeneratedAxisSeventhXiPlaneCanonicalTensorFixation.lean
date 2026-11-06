/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneTensorReturnExact

/-! The exhaustive integer return fixes every coordinate of the genuine canonical tensor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency true

/-- The original corrected local lift fixes the full canonical tensor,
with its exact normalization. -/
theorem generatedSeventhXiPlaneCanonicalTensor_fixed :
    localTensorRepresentation generatedSeventhXiPlaneFiber
      (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.2 =
      (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.2 := by
  have he : (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.2 =
      (1 / (32 * Real.sqrt 2) : ℝ) •
        (fun t i => (generatedSeventhXiPlaneTensorPacked (nortonUIntegerLabel t) i : ℝ)) := by
    funext t i
    rw [generatedSeventhXiPlaneTensorPacked_actual]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, map_smul]
  funext t i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [generatedSeventhXiPlane_integer_tensor_embed, generatedSeventhXiPlaneIntegerTensor_fixed]
  push_cast
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
