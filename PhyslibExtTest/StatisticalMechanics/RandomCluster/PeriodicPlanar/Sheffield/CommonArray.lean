/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.CommonArray

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.CommonArray`

* `boundaryGridBase`, `boundaryGridWidth` and `boundaryGridHeight` evaluate on explicit sites.
* `exists_deep_common_preference_grid_witness` on the `2 × 2` grid with margin `0` and the
  bottom-row / left-column labelings.
* `exists_commonPreferenceExtents_ge` with all placements at the origin and minima `1`.
* `PeriodicPlaneEmbedding.exists_uniformRadius_deepGridPreference_crossing_max_tendsto_one`
  elaborates (check-only; no concrete plane embedding is available).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.CommonArray

open _root_.StatMech.FK.PeriodicPlanar _root_.StatMech.Lattice

-- The grid base takes the left placement's `x` and the bottom placement's `y`.
example : boundaryGridBase ![1, 2] ![3, 4] = ![1, 4] := by
  funext i
  fin_cases i <;> simp [boundaryGridBase]

-- Width and height of the grid spanned by placements at the origin with extent `3`.
example : boundaryGridWidth 3 0 0 = 3 ∧ boundaryGridHeight 3 0 0 = 3 := by
  simp [boundaryGridWidth, boundaryGridHeight]

-- A deep witness on the `2 × 2` grid with margin `0`.
example : ∃ x xV xH : PreferenceGridVertex 1 1,
    decide (x.2.val = 0) = true ∧ decide (x.1.val = 0) = true ∧
    KingAdj (preferenceGridSite x) (preferenceGridSite xV) ∧ decide (xV.2.val = 0) = false ∧
    KingAdj (preferenceGridSite x) (preferenceGridSite xH) ∧ decide (xH.1.val = 0) = false ∧
    0 ≤ x.1.val ∧ x.1.val + 0 < 1 ∧ 0 ≤ x.2.val ∧ x.2.val + 0 < 1 :=
  exists_deep_common_preference_grid_witness one_pos
    (fun v => decide (v.2.val = 0)) (fun v => decide (v.1.val = 0))
    (fun _ h => decide_eq_true (by omega)) (fun _ h => decide_eq_false (by omega))
    (fun _ h => decide_eq_true (by omega)) (fun _ h => decide_eq_false (by omega))

-- Nondegenerate common extents exist above any minima.
example : ∃ eX eY : ℕ, 1 ≤ eX ∧ 1 ≤ eY ∧
    0 < (0 : Site 2) 0 + (eX : ℤ) - (0 : Site 2) 0 ∧
    0 < (0 : Site 2) 0 + (eX : ℤ) - (0 : Site 2) 0 ∧
    0 < (0 : Site 2) 1 + (eY : ℤ) - (0 : Site 2) 1 ∧
    0 < (0 : Site 2) 1 + (eY : ℤ) - (0 : Site 2) 1 :=
  exists_commonPreferenceExtents_ge 0 0 0 0 0 0 0 0 1 1

open PeriodicPlaneEmbedding in
example := @exists_uniformRadius_deepGridPreference_crossing_max_tendsto_one

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.CommonArray
