/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BernoulliErgodicFiniteEnergy

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BernoulliErgodicFiniteEnergy`

* `bkc_bernoulli_hasFiniteEnergyMerge` and `bkc_bernoulli_isErgodic` at `p = 1/2`;
* `bkc_boxFinsetBK_card_pos` and `bkc_boundary_vol_ratio_le` at explicit sizes;
* `bkc_boundary_vol_tendsto` for `d = 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BernoulliErgodicFiniteEnergy

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation
open scoped NNReal

-- Bernoulli(1/2) bond percolation on `ℤ²` has the finite-energy merge property.
example := bkc_bernoulli_hasFiniteEnergyMerge (d := 2) (1 / 2 : ℝ≥0) (by norm_num) (by norm_num)

-- Bernoulli(1/2) bond percolation on `ℤ²` is ergodic.
example := bkc_bernoulli_isErgodic (d := 2) (by norm_num) (1 / 2 : ℝ≥0) (by norm_num)

-- Boxes are nonempty, and the boundary-to-volume ratio of the box of radius 4 is at most 1.
example : 0 < (boxFinsetBK 2 3).card := bkc_boxFinsetBK_card_pos 2 3
example : (boxSV_boundaryCard 2 4 : ℝ) / ((boxFinsetBK 2 4).card : ℝ) ≤ (2 * 2 : ℝ) / 4 :=
  bkc_boundary_vol_ratio_le 2 4 (by norm_num) (by norm_num)

-- The boundary-to-volume ratio tends to zero.
example : Filter.Tendsto (fun n => (boxSV_boundaryCard 2 n : ℝ) / ((boxFinsetBK 2 n).card : ℝ))
    Filter.atTop (nhds 0) :=
  bkc_boundary_vol_tendsto 2 (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BernoulliErgodicFiniteEnergy
