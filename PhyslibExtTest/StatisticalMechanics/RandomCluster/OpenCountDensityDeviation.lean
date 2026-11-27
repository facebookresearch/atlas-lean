/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.OpenCountDensityDeviation

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.OpenCountDensityDeviation`

In `ℤ²` at `p = 1/2` (`q = 2`), box radius `1`:
* `ivd_freeEdgeDensity_nonneg`, `ivd_freeEdgeDensity_le_one`, `ivd_wiredEdgeDensity_le_one`;
* `ivd_freeAvgDensity_nonneg`;
* `free_openCount_le_avgDensity_add_prob_ge` and `wired_openCount_ge_avgDensity_sub_prob_ge` in
  conditional form (given the size conditions on `ε` and a nonempty edge set).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.OpenCountDensityDeviation

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

-- Edge densities lie in `[0, 1]`.
example (e : Sym2 (boxVerts 2 1)) :
    0 ≤ freeEdgeDensity 2 2 (edgeIncl 2 1 e) (1 / 2) ∧
      freeEdgeDensity 2 2 (edgeIncl 2 1 e) (1 / 2) ≤ 1 ∧
      wiredEdgeDensity 2 2 (edgeIncl 2 1 e) (1 / 2) ≤ 1 :=
  ⟨ivd_freeEdgeDensity_nonneg 1 e (by norm_num) (by norm_num),
   ivd_freeEdgeDensity_le_one 1 e (by norm_num) (by norm_num),
   ivd_wiredEdgeDensity_le_one 1 e (by norm_num) (by norm_num)⟩

-- The average free density is nonnegative.
example : 0 ≤ ivd_freeAvgDensity 2 1 (1 / 2) :=
  ivd_freeAvgDensity_nonneg 1 (by norm_num) (by norm_num)

-- Free upper deviation of the open-edge count.
example {ε : ℝ} (hε : 0 < ε) (hεa : ε ≤ 1 - ivd_freeAvgDensity 2 1 (1 / 2))
    (hE : 0 < ((boxGraph 2 1).edgeFinset.card : ℝ)) :=
  free_openCount_le_avgDensity_add_prob_ge 1 (by norm_num) (by norm_num) hε hεa hE

-- Wired lower deviation of the open-edge count.
example {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ ivd_wiredAvgDensity 2 1 (1 / 2))
    (hE : 0 < ((boxGraph 2 1).edgeFinset.card : ℝ)) :=
  wired_openCount_ge_avgDensity_sub_prob_ge 1 (by norm_num) (by norm_num) hε hεb hE

end PhyslibExtTest.StatisticalMechanics.RandomCluster.OpenCountDensityDeviation
