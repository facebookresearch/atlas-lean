/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketPackedEvaluation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder

/-! Ordinary-kernel source checks retain every occurring octad and every original Fourier sign. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- All original occurring source codes, including the omega coordinate, are retained.
/-- Every packed octad code is its complete genuine original source label. -/
theorem generatedSeventhXiShortPackedOctadCode_actual : ∀ g : Fin 231,
    generatedSeventhXiShortPackedOctadCode g = generatedSeventhXiOctadCode g := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- The already proved all-label theta evaluator binds this finite source cache.
/-- Every packed theta is the original full Parker theta of its occurring source code. -/
theorem generatedSeventhXiShortPackedOctadTheta_actual : ∀ g : Fin 231,
    generatedSeventhXiShortPackedOctadTheta g =
      generatedSeventhXiShortThetaSplit (generatedSeventhXiShortPackedOctadCode g) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Check all eight genuine ordered physical coordinates of every occurring octad.
/-- Every packed physical coordinate is its original source coordinate. -/
theorem generatedSeventhXiShortPackedOctadCoordinate_actual : ∀ g : Fin 231, ∀ k : Fin 8,
    generatedSeventhXiShortPackedOctadCoordinate g k =
      generatedSeventhXiOctadCoordinates g k := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- All original sign slots, including the absent-slot sentinel, are checked.
/-- Packed signs and signed integer weights retain every original preferred-Q phase. -/
theorem generatedSeventhXiShortPackedOctadSlot_actual : ∀ g : Fin 231, ∀ k : Fin 3,
    generatedSeventhXiShortPackedOctadSign g k =
      (⟨generatedSeventhXiOctadSigns g k % 64, Nat.mod_lt _ (by decide)⟩ : Fin 64) ∧
    generatedSeventhXiShortPackedOctadWeight g k = generatedSeventhXiOctadWeights g k := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Check every entry of the original sixty-four by sixty-four operator.
/-- Every packed Fourier sign is the complete original integer octad operator entry. -/
theorem generatedSeventhXiShortPackedFourierSign_actual : ∀ e f : Fin 64,
    generatedSeventhXiShortPackedFourierSign e f = trialityIntegerMatrix e f := by
  unfold trialityIntegerMatrix trialityHadamard
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- All original octad sign representatives and their source half-weight parity are checked.
/-- The packed omega bit is the genuine source translation correction. -/
theorem generatedSeventhXiShortPackedOmega_actual : ∀ e : Fin 64,
    golayBooleanCast (generatedSeventhXiShortPackedOmega e) = griessOctadOmegaCoefficient e := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
