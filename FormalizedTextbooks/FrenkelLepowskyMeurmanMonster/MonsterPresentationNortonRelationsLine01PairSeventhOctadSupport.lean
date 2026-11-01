/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact sixteen-entry supports in each reached seventh-state octad block. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairSeventhData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The sixteen original even-sign labels in each nonzero reached octad support. -/
def monsterNortonLine01PairSeventhOctadSupport : Fin 14 → Fin 16 → Fin 64 :=
  ![![4, 7, 8, 11, 17, 18, 29, 30, 33, 34, 45, 46, 52, 55, 56, 59],
    ![4, 7, 8, 11, 17, 18, 29, 30, 33, 34, 45, 46, 52, 55, 56, 59],
    ![4, 7, 8, 11, 17, 18, 29, 30, 33, 34, 45, 46, 52, 55, 56, 59],
    ![0, 3, 12, 15, 21, 22, 25, 26, 37, 38, 41, 42, 48, 51, 60, 63],
    ![5, 6, 9, 10, 16, 19, 28, 31, 32, 35, 44, 47, 53, 54, 57, 58],
    ![4, 7, 8, 11, 17, 18, 29, 30, 33, 34, 45, 46, 52, 55, 56, 59],
    ![1, 2, 13, 14, 20, 23, 24, 27, 36, 39, 40, 43, 49, 50, 61, 62],
    ![4, 7, 8, 11, 17, 18, 29, 30, 33, 34, 45, 46, 52, 55, 56, 59],
    ![4, 7, 8, 11, 17, 18, 29, 30, 33, 34, 45, 46, 52, 55, 56, 59],
    ![4, 7, 8, 11, 17, 18, 29, 30, 33, 34, 45, 46, 52, 55, 56, 59],
    ![4, 7, 8, 11, 17, 18, 29, 30, 33, 34, 45, 46, 52, 55, 56, 59],
    ![1, 2, 13, 14, 20, 23, 24, 27, 36, 39, 40, 43, 49, 50, 61, 62],
    ![0, 3, 12, 15, 21, 22, 25, 26, 37, 38, 41, 42, 48, 51, 60, 63],
    ![5, 6, 9, 10, 16, 19, 28, 31, 32, 35, 44, 47, 53, 54, 57, 58]]

/-- All signed nonzero octad numerators, in exactly that support order. -/
def monsterNortonLine01PairSeventhOctadSupportCoefficient : Fin 14 → Fin 16 → ℤ :=
  ![![-1, -1, -1, -1, 1, -1, -1, 1, -1, 1, 1, -1, -1, -1, -1, -1],
    ![-1, -1, -1, -1, 1, -1, -1, 1, -1, 1, 1, -1, -1, -1, -1, -1],
    ![-1, -1, -1, -1, 1, -1, -1, 1, -1, 1, 1, -1, -1, -1, -1, -1],
    ![-1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, -1, -1, 1],
    ![-1, -1, -1, -1, -1, 1, 1, -1, 1, -1, -1, 1, -1, -1, -1, -1],
    ![-1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, -1, -1, 1],
    ![-1, -1, -1, -1, -1, 1, 1, -1, 1, -1, -1, 1, -1, -1, -1, -1],
    ![1, 1, 1, 1, -1, 1, 1, -1, 1, -1, -1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, -1, 1, 1, -1, 1, -1, -1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, -1, 1, 1, -1, 1, -1, -1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, -1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1],
    ![1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, -1],
    ![1, 1, 1, 1, 1, -1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1],
    ![1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, -1]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Check every nonzero and zero coefficient against the complete original sixty-four-entry rows.
/-- The sixteen-entry display equals the complete checked original octad row. -/
theorem monsterNortonLine01PairSeventhOctadSupport_certificate (a : Fin 14) (r : Fin 64) :
    (∑ j : Fin 16, if monsterNortonLine01PairSeventhOctadSupport a j = r then
      monsterNortonLine01PairSeventhOctadSupportCoefficient a j else 0) =
        monsterNortonLine01PairSeventhOctadNumerator a r := by
  revert a r
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
