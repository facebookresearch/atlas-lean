/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiOctadPacket00Data

/-! Original physical, source-Q, signed phase and coefficient checks for the first octad packet. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Finite checks retain both the original Q base and its central coefficient. -/
local instance generatedSixthXiOctadPacket00QDecidable : DecidableEq Q :=
  generatedSixthQDecidableEq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
-- Check 16 complete original physical rows, source lifts, full phases and true signed numerators.
/-- All checked original scalar and physical data satisfy the complete preferred transport. -/
theorem generatedSixth_xi_octad_packet00_certificate (a : Fin 16) :
    let e : Fin 64 := ⟨a.val, by omega⟩
    generatedSixthXiShortIntegerQ (generatedSixthXiOctadPacket00InputIntegral e) =
      generatedSixthXiPackedQ (generatedSixthXiOctadPacket00SourceMasks e) ∧
    (sixthFrameOrbitSpatialNumerator 14 *ᵥ generatedSixthXiOctadPacket00InputIntegral e =
      fun i => 2 * nortonUIntegerSign (generatedSixthXiOctadPacket00PhysicalPhase e) *
        generatedSixthXiOctadPacket00OutputIntegral e i) ∧
    generatedSixthXiSelectedPhase
      (generatedSixthXiPackedQ (generatedSixthXiOctadPacket00SourceMasks e)) =
      generatedSixthXiOctadPacket00Phase e ∧
    nortonUIntegerSign (generatedSixthXiOctadPacket00Phase e) *
      generatedSixthFinalOctadCachedNumerator 190 e =
        generatedSixthFinalOctadCachedNumerator
          (generatedSixthXiOctadPacket00OutputAddress e).1
          (generatedSixthXiOctadPacket00OutputAddress e).2 := by
  revert a
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
