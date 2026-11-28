/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MergeFreeTrifurcation

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.MergeFreeTrifurcation`

* `tfx_htrif_of_mergeFree` and `bkc_htrif_bernoulli` as conditional statements in `ℤ²`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MergeFreeTrifurcation

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation MeasureTheory
open scoped NNReal

-- Merge-freeness gives positive trifurcation probability.
example (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hmf : ∀ (n : ℕ) (ω : ConfigSpace (Sym2 (Site 2))), ω ∈ threeMeetBox 2 n → bka_MergeFree ω)
    (htop : 0 < μ {ω | numInfiniteClusters 2 ω = ⊤}) :
    0 < μ {ω | IsTrifurcation 2 ω 0} :=
  tfx_htrif_of_mergeFree μ hfe hmf htop

-- The Bernoulli form.
example (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hmf : ∀ (n : ℕ) (ω : ConfigSpace (Sym2 (Site 2))), ω ∈ threeMeetBox 2 n → bka_MergeFree ω)
    (htop : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      {ω | numInfiniteClusters 2 ω = ⊤}) :
    0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 {ω | IsTrifurcation 2 ω 0} :=
  bkc_htrif_bernoulli p hp1 hp0 hmf htop

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.MergeFreeTrifurcation
