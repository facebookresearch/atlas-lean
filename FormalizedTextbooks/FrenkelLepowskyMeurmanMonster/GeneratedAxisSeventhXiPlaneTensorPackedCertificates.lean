/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneTensorPackedData

/-! Every packed tensor entry equals its complete original source-bound coefficient. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Check every entry of this complete original coefficient table.
/-- All signed positions match the complete original sparse odd rows. -/
theorem generatedSeventhXiTensorPacked_odd_slots : ∀ g : Fin 232, ∀ k : Fin 3,
    generatedSeventhXiTensorOddWeight g k = generatedSeventhXiOddWeights g k ∧
    generatedSeventhXiTensorOddPosition g k = generatedSeventhXiOddPositions g k := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Check every entry of this complete original coefficient table.
/-- Every physical mask is the complete original Golay encoding. -/
theorem generatedSeventhXiTensorPacked_mask : ∀ d : Fin 2048,
    generatedSeventhXiTensorMask d = golayEncodedMask d.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Check every entry of this complete original coefficient table.
/-- Every quarter-weight sign retains the original exact physical-code phase. -/
theorem generatedSeventhXiTensorPacked_kappa : ∀ d : Fin 2048,
    generatedSeventhXiTensorKappa d =
      nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Check every entry of this complete original coefficient table.
/-- All normalized spin coefficients retain the original support and signed phases. -/
theorem generatedSeventhXiTensorPacked_spin : ∀ d : Fin 4096,
    generatedSeventhXiTensorSpin d = generatedSeventhXiPlaneSpinInteger d := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Check every entry of this complete original coefficient table.
/-- Every spatial coefficient is the original integral word-image coordinate. -/
theorem generatedSeventhXiTensorPacked_frame : ∀ i : Fin 24,
    generatedSeventhXiTensorFrame i = generatedSeventhFrameVectorData 7 0 i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
