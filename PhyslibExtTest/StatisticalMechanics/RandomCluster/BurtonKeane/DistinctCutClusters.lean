/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DistinctCutClusters

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DistinctCutClusters`

In the plane:
* `bc8_distinctCutClusters`: `bc8_DistinctCutClusters 2 n` holds, here at `n = 4`;
* `bc8_threeArmClusters_distinct` in conditional form on `threeMeetBox 2 4`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.DistinctCutClusters

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

-- Distinct infinite cut clusters exist for the radius-4 box.
example : bc8_DistinctCutClusters 2 4 :=
  bc8_distinctCutClusters 4

-- A configuration meeting the box in three infinite clusters has three distinct cut clusters.
example (ω : ConfigSpace (Sym2 (Site 2))) (hω : ω ∈ threeMeetBox 2 4) : ∃ x₁ x₂ x₃ : Site 2,
    (cluster 2 (removeSite 0 ω) x₁).Infinite ∧ (cluster 2 (removeSite 0 ω) x₂).Infinite ∧
    (cluster 2 (removeSite 0 ω) x₃).Infinite ∧
    cluster 2 (removeSite 0 ω) x₁ ≠ cluster 2 (removeSite 0 ω) x₂ ∧
    cluster 2 (removeSite 0 ω) x₁ ≠ cluster 2 (removeSite 0 ω) x₃ ∧
    cluster 2 (removeSite 0 ω) x₂ ≠ cluster 2 (removeSite 0 ω) x₃ :=
  bc8_threeArmClusters_distinct 4 ω hω

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.DistinctCutClusters
