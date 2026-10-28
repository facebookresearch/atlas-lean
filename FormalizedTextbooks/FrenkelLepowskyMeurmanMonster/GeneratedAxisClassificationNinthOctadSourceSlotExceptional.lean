/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotFourierData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadMarkingData

/-! Exact candidate integer Fourier computation at the only eight-term source block.
Actual source coefficients and source-word phases remain separate certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- The full original sixty-four-row integer Fourier check exceeds the default budget.
/-- The original eight-term integer Fourier calculation has numerator minus16 precisely
at the displayed signs, and every other numerator is bounded by four. -/
theorem generatedNinth_octad_exceptional_integer : ∀ e : Fin 64,
    if e ∈ generatedNinthOctadMarkedSigns then
      generatedNinthFinalOctadSlotFastNumerator 459 e = -16
    else |generatedNinthFinalOctadSlotFastNumerator 459 e| ≤ 4 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
