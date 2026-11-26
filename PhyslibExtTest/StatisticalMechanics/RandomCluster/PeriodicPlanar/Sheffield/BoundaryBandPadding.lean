/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.BoundaryBandPadding

/-!
# Tests for `Sheffield.BoundaryBandPadding`

Module under test: `Sheffield.BoundaryBandPadding` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

With margin `1` and extent `4`:
* `boundaryBandPreferenceColor` is `true` at position `0` (lower band) and `false` at position `3`
  (upper band);
* `boundaryBandPreferenceColor_true_imp` and `boundaryBandPreferenceColor_false_imp` apply at
  those positions with scores `1`, threshold `p = 1` and `ε = 0`;
* `PeriodicPlaneEmbedding.exists_translatedFamily_leftBoundaryExhaustion_measureReal_gt`
  elaborates (check-only; no concrete plane embedding is available).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace BoundaryBandPadding

open _root_.StatMech.FK.PeriodicPlanar

/-- Position `0` lies in the lower band. -/
theorem color_zero : boundaryBandPreferenceColor 1 4 0 0 1 1 = true := by
  simp [boundaryBandPreferenceColor]

/-- Position `3` lies in the upper band. -/
theorem color_three : boundaryBandPreferenceColor 1 4 3 0 1 1 = false := by
  simp [boundaryBandPreferenceColor]

-- A `true` position satisfies the preference inequality.
example : (1 : ℝ) ≤ 1 + 0 :=
  boundaryBandPreferenceColor_true_imp (p := 1) le_rfl (by norm_num) le_rfl (fun _ => le_rfl)
    (by norm_num) color_zero

-- A `false` position satisfies the opposite inequality.
example : (1 : ℝ) ≤ 1 + 0 :=
  boundaryBandPreferenceColor_false_imp (p := 1) le_rfl (by norm_num) le_rfl (fun _ => le_rfl)
    (by norm_num) color_three

open PeriodicPlaneEmbedding in
example := @exists_translatedFamily_leftBoundaryExhaustion_measureReal_gt

end BoundaryBandPadding
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
