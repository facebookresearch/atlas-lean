/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketPackedEvaluation

/-! Complete source syndromes of the physical negative positions in every occurring octad. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The original even-sign mask placed at the packed increasing physical octad coordinates. -/
def generatedSeventhXiShortPackedNegativeMask (g : Fin 231) (e : Fin 64) : ℕ :=
  (List.finRange 8).foldr (fun k m =>
    (if (trialityEvenMask e).testBit k.val then
      2 ^ (generatedSeventhXiShortPackedOctadCoordinate g k).val else 0) ||| m) 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Check the complete physical syndrome for every sign of every occurring family.
/-- The cached syndrome retains all original physical negative positions and Golay cocode bits. -/
theorem generatedSeventhXiShortPackedOctadSyndrome_actual : ∀ g : Fin 231, ∀ e : Fin 64,
    generatedSeventhXiShortPackedOctadSyndrome g e =
      generatedSeventhXiShortSyndromeMask (generatedSeventhXiShortPackedNegativeMask g e) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
