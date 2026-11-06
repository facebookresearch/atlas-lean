/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete eighth octad rows and their exact actual inverse-triality transforms. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairEighthCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOctadTrialityInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All original sixty-four source numerators in each of the two reached eighth octads. -/
def monsterNortonLine01PairEighthOctadNumerator : Fin 2 → Fin 64 → ℤ :=
  ![![
      -1, -1, 1, -1, -1, 1, -1, -1, -1, 1, -1, -1, 1, 1, -1, 1,
      1, -1, 1, 1, -1, -1, 1, -1, -1, -1, 1, -1, -1, 1, -1, -1,
      -1, 1, -1, -1, 1, 1, -1, 1, 1, 1, -1, 1, 1, -1, 1, 1,
      -1, -1, 1, -1, -1, 1, -1, -1, -1, 1, -1, -1, 1, 1, -1, 1],
    ![
      -1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1, -1, -1, -1, 1, -1,
      -1, 1, -1, -1, -1, -1, 1, -1, 1, 1, -1, 1, -1, 1, -1, -1,
      -1, 1, -1, -1, -1, -1, 1, -1, 1, 1, -1, 1, -1, 1, -1, -1,
      1, 1, -1, 1, -1, 1, -1, -1, 1, -1, 1, 1, 1, 1, -1, 1]]

/-- The original even-sign coordinates of the two surviving ninth-state octad units. -/
def monsterNortonLine01PairNinthOctadTarget : Fin 2 → Fin 64 := ![45, 57]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Check every output coordinate against all 240 true signed source contributions.
/-- Every entire reached octad row includes precisely its actual source coefficients. -/
theorem monsterNortonLine01PairEighthOctadNumerator_certificate (a : Fin 2) (r : Fin 64) :
    (∑ k : Fin 240, if monsterNortonLine01PairEighthIsPair k then 0 else
      if monsterNortonLine01PairEighthOctadSlot k = a ∧
        monsterNortonLine01PairEighthOctadSign k = r then
          monsterNortonLine01PairEighthCoefficient k else 0) =
      monsterNortonLine01PairEighthOctadNumerator a r := by
  revert a r
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Verify all 128 actual inverse Fourier outputs, including every zero.
/-- Inverse extra sends both complete octad rows to exactly their single surviving units. -/
theorem monsterNortonLine01PairNinthOctadNumerator_certificate (a : Fin 2) (r : Fin 64) :
    (∑ s : Fin 64, monsterNortonLine01PairEighthOctadNumerator a s *
      monsterNortonOctadInverseCoefficient r s) =
        if r = monsterNortonLine01PairNinthOctadTarget a then -64 else 0 := by
  revert a r
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
