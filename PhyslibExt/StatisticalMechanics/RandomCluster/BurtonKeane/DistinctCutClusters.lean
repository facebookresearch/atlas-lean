/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCutNeighbour
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutDistinctWitnessClusters

/-!
# Three distinct cut clusters

Every configuration with three infinite clusters meeting a box has three sites with infinite,
pairwise distinct cut clusters.

## i. Overview

`bc8_DistinctCutClusters d n` asks every configuration of `threeMeetBox d n` for three sites of the
box in distinct infinite clusters with sites whose cut clusters are infinite and pairwise distinct.
It holds for every `n`.

## ii. Key results

- `bc8_threeArmClusters_distinct` : three distinct infinite cut clusters.

## iii. Table of contents

- A. Distinct cut clusters

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}

/-! ## A. Distinct cut clusters -/

/-- Every configuration of `threeMeetBox d n` has three sites of the box in distinct infinite
clusters,
with sites whose cut clusters are infinite and pairwise distinct. Same statement as
`bc7_DistinctWitnessClusters`; kept because replacing a definition changes the statements that
mention it. -/
def bc8_DistinctCutClusters (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∃ x₁ x₂ x₃ : Site d, x₁ ∈ box d n ∧ x₂ ∈ box d n ∧ x₃ ∈ box d n ∧
      (cluster d ω x₁).Infinite ∧ (cluster d ω x₂).Infinite ∧ (cluster d ω x₃).Infinite ∧
      cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧
      cluster d ω x₂ ≠ cluster d ω x₃ ∧
      ∃ x₁' x₂' x₃' : Site d, x₁' ∈ cluster d ω x₁ ∧ x₂' ∈ cluster d ω x₂ ∧
        x₃' ∈ cluster d ω x₃ ∧
        (cluster d (removeSite 0 ω) x₁').Infinite ∧
        (cluster d (removeSite 0 ω) x₂').Infinite ∧
        (cluster d (removeSite 0 ω) x₃').Infinite ∧
        cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₂' ∧
        cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₃' ∧
        cluster d (removeSite 0 ω) x₂' ≠ cluster d (removeSite 0 ω) x₃'

lemma bc8_distinctCutClusters (n : ℕ) : bc8_DistinctCutClusters d n :=
  bc7_distinctWitnessClusters n

lemma bc8_threeArmClusters_distinct (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hω : ω ∈ threeMeetBox d n) :
    ∃ x₁' x₂' x₃' : Site d,
      (cluster d (removeSite 0 ω) x₁').Infinite ∧
      (cluster d (removeSite 0 ω) x₂').Infinite ∧
      (cluster d (removeSite 0 ω) x₃').Infinite ∧
      cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₂' ∧
      cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₃' ∧
      cluster d (removeSite 0 ω) x₂' ≠ cluster d (removeSite 0 ω) x₃' := by
  obtain ⟨_x₁, _x₂, _x₃, _hb1, _hb2, _hb3, _hi1, _hi2, _hi3, _hd12, _hd13, _hd23,
      x₁', x₂', x₃', _hx₁', _hx₂', _hx₃', hinf₁, hinf₂, hinf₃, hcd12, hcd13, hcd23⟩ :=
    bc8_distinctCutClusters n ω hω
  exact ⟨x₁', x₂', x₃', hinf₁, hinf₂, hinf₃, hcd12, hcd13, hcd23⟩

end Walls

end StatMech
