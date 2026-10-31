/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TorusComparison

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.TorusComparison`

On the torus of side `L = 3`:
* at `q = 1` the defect-weighted dual partition sum equals the plain one (sector sums);
* `triHexTorus_defectWeighted_partition_bounds` at `p = 1 / 2`, `q = 2`;
* `triHexTorus_partition_duality_defectWeighted` at `p = 1 / 2`, `q = 2`;
* `triHexTorus_topologicalCorrection_logDensity_tendsto_zero` at `q = 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.TorusComparison

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.FK.PeriodicPlanar

instance : Fact (2 < 3) := ⟨by norm_num⟩

-- At `q = 1` the topological weight disappears.
example (pDual : ℝ) :
    triHexTorusDefectWeightedDualPartitionSum 3 pDual 1 =
      triHexTorusDualPartitionSum 3 pDual 1 := by
  rw [triHexTorusDefectWeightedDualPartitionSum_eq_sectorSum,
    triHexTorusDualPartitionSum_eq_sectorSum, one_mul, one_pow, one_mul]

-- The defect-weighted sum is within a factor `q²` of the plain dual sum.
example := triHexTorus_defectWeighted_partition_bounds 3 (p := 1 / 2) (q := 2)
  (by norm_num) (by norm_num) (by norm_num)

-- Exact partition-function duality on the triangular torus of side `3`.
example := triHexTorus_partition_duality_defectWeighted 3 (p := 1 / 2) (q := 2)
  (by norm_num) (by norm_num) (by norm_num)

-- The topological correction to the free energy per site vanishes.
example (omega : ∀ L : ℕ, ConfigSpace (Sym2 (TorusSite L))) :
    Filter.Tendsto (triHexTorusTopologicalCorrectionLogDensity 2 omega) Filter.atTop (nhds 0) :=
  triHexTorus_topologicalCorrection_logDensity_tendsto_zero 2 (by norm_num) omega

end PhyslibExtTest.StatisticalMechanics.RandomCluster.TriHex.TorusComparison
