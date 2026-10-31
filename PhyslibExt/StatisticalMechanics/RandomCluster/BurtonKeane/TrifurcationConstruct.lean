/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoundaryVolumeRatio
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BurtonKeaneAttachment
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HighDimRouting
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationConstruction

/-!
# Trifurcations from merge-free configurations

If every configuration with three distinct infinite clusters is merge-free at the origin, Bernoulli
measures give trifurcations with positive probability when `N = ∞`.

## i. Overview

`bka_MergeFree ω` gives three neighbours of the origin reaching three distinct infinite clusters
without merging. Under Bernoulli measures with `0 < p` finite modifications cost positive
probability, so merge-freeness of every configuration in `threeMeetBox` discharges the trifurcation
input `htrif` of the counting argument.

## ii. Key results

- `tfx_htrif_of_mergeFree` : merge-freeness discharges the trifurcation input
- `bkc_htrif_bernoulli` : the Bernoulli form of the trifurcation input

## iii. Table of contents

- A. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

open DisjointPaths

variable {d : ℕ}

/-! ## A. Results -/

lemma tfx_htrif_of_mergeFree
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hmf : ∀ (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))),
      ω ∈ threeMeetBox d n → bka_MergeFree ω) :
    0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsTrifurcation d ω 0} := by
  refine htrif_discharged μ hfe ?_
  refine hrHD_route_of_routing μ hfe ?_
  intro n
  exact bka_routing_of_mergeFree n (fun ω hω => hmf n ω hω)

lemma bkc_htrif_bernoulli (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hmf : ∀ (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))),
      ω ∈ threeMeetBox d n → bka_MergeFree ω) :
    0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0} :=
  tfx_htrif_of_mergeFree (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0) hmf

end Percolation

end StatMech
