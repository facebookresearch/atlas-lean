/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorLiteralData

/-! A full64-sign original octad row is bound to the complete sparse physical packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

/-- Every sign and both complete intermediate stages of this actual code row are retained. -/
theorem generatedFeasibleContainingZeroOutsideAnchorOctadRow01_sparse : ∀ t : Fin 2, ∀ e : Fin 64,
    generatedFeasibleContainingZeroOutsideAnchorOctadQ (if t = 0 then 1 else 2) (generatedFeasibleContainingZeroOutsideAnchorCode 1) e =
      generatedFeasibleContainingZeroOutsideAnchorOctadLiteralQ t 1 e := by decide +kernel

/-- All64 output signs follow from the actual original Fourier operator on the full64 input signs. -/
theorem generatedFeasibleContainingZeroOutsideAnchorOctadRow01_fourier : ∀ e : Fin 64,
    (∑ f : Fin 64, (trialityIntegerMatrix e f : ℚ) / 8 *
      generatedFeasibleContainingZeroOutsideAnchorOctadLiteralQ 0 1 f) =
        generatedFeasibleContainingZeroOutsideAnchorOctadLiteralQ 1 1 e := by decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
