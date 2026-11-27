/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.BoundaryGrid

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.BoundaryGrid`

* `rectangleEndpointPreferenceError_le_boundaryProbabilities` on the `2 × 2` grid with all scores
  `1` and all thresholds `1` (the bound is `0`).
* `exists_cofinalIndex_weightedFourDefects_tendsto_zero` for constant-`1` scores and explicit
  growing widths `n` and heights `2 n`.
* `PeriodicPlaneEmbedding.exists_uniformTemplate_boundaryScores_crossing_max_tendsto_one`
  elaborates (check-only; no concrete plane embedding is available).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.BoundaryGrid

open _root_.StatMech.FK.PeriodicPlanar Filter

-- Perfect boundary scores: the preference error is bounded by `0`.
example : rectangleEndpointPreferenceError (n := 1) (m := 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (fun _ => 1) ≤
      ((1 : ℕ) + 1 : ℝ) * (1 - 1) + ((1 : ℕ) + 1 : ℝ) * (1 - 1) +
        ((1 : ℕ) + 1 : ℝ) * (1 - 1) + ((1 : ℕ) + 1 : ℝ) * (1 - 1) :=
  rectangleEndpointPreferenceError_le_boundaryProbabilities _ _ _ _ 1 1 1 1 le_rfl le_rfl le_rfl
    le_rfl (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)

-- A cofinal index sequence for constant-`1` scores and widths `n`, heights `2 n`.
example : ∃ index : ℕ → ℕ, (∀ n, n ≤ index n) ∧
    Tendsto (fun n : ℕ =>
      ((n : ℕ) + 1 : ℝ) * (1 - (fun _ => (1 : ℝ)) (index n)) +
      ((n : ℕ) + 1 : ℝ) * (1 - (fun _ => (1 : ℝ)) (index n)) +
      ((2 * n : ℕ) + 1 : ℝ) * (1 - (fun _ => (1 : ℝ)) (index n)) +
      ((2 * n : ℕ) + 1 : ℝ) * (1 - (fun _ => (1 : ℝ)) (index n))) atTop (nhds 0) :=
  exists_cofinalIndex_weightedFourDefects_tendsto_zero _ _ _ _ tendsto_const_nhds
    tendsto_const_nhds tendsto_const_nhds tendsto_const_nhds (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun n => n) (fun n => 2 * n)

open PeriodicPlaneEmbedding in
example := @exists_uniformTemplate_boundaryScores_crossing_max_tendsto_one

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.BoundaryGrid
