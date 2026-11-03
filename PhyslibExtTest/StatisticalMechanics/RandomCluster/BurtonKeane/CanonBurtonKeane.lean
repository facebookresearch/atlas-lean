/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonBurtonKeane

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonBurtonKeane`

* `cbk_boundary_succ_vol_tendsto` for `d = 2`;
* `cbk_canonical_trif_prob_eq_zero` for Bernoulli(1/2) bond percolation on `ℤ²` (translation
  invariance from `bkc_bernoulli_isErgodic`);
* `cbk_canonical_uniqueness` for Bernoulli(1/2) in conditional form (only the trifurcation
  hypothesis assumed).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CanonBurtonKeane

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation
open scoped NNReal

-- The shifted boundary-to-volume ratio tends to zero.
example : Filter.Tendsto
    (fun n => (boxSV_boundaryCard 2 (n + 1) : ℝ) / ((boxFinsetBK 2 n).card : ℝ))
    Filter.atTop (nhds 0) :=
  cbk_boundary_succ_vol_tendsto 2 (by norm_num)

-- Canonical trifurcations have probability zero under Bernoulli(1/2) on `ℤ²`.
example : bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2 : ℝ≥0) (by norm_num)
    {ω | IsCanonicalTrifurcation 2 ω 0} = 0 :=
  cbk_canonical_trif_prob_eq_zero _ (by norm_num)
    (bkc_bernoulli_isErgodic (by norm_num) (1 / 2 : ℝ≥0) (by norm_num)).1

-- Uniqueness for Bernoulli(1/2) from the trifurcation hypothesis.
example (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2 : ℝ≥0) (by norm_num)
      {ω | numInfiniteClusters 2 ω = ⊤} →
    0 < bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2 : ℝ≥0) (by norm_num)
      {ω | IsCanonicalTrifurcation 2 ω 0}) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2 : ℝ≥0) (by norm_num)
      (atLeastTwoInfinite 2) = 0 :=
  (cbk_canonical_uniqueness _ (by norm_num)
    (bkc_bernoulli_isErgodic (by norm_num) (1 / 2 : ℝ≥0) (by norm_num))
    (bkc_bernoulli_hasFiniteEnergyMerge _ (by norm_num) (by norm_num)) htrif).2.1

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CanonBurtonKeane
