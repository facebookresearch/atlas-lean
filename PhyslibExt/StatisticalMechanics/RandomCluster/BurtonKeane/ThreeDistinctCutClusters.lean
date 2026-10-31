/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalOriginRewiring
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DistinctCutClusters
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DisjointCutNoCrossing

/-!
# Three distinct clusters after removing the origin

Every configuration in `threeMeetBox d n` has three distinct infinite clusters after removing the
origin, and their arms do not cross.

## i. Overview

`bc9_DistinctCutClusters d n` asks for three sites whose clusters in `removeSite 0 ω` are infinite
and pairwise distinct. It holds for every `n`, the three arms are pairwise distinct and do not
merge, and with origin rewiring the origin becomes a canonical trifurcation after a finite rewiring
away from it.

## ii. Key results

- `bc9_distinctCutClusters` : three distinct infinite clusters after removing the origin
- `StatMech.Walls.bc7_cut_no_crossing` (in `CutClusterNoCrossing`) : the arms do not cross
- `StatMech.Walls.bc8_canonicalTrif_of_originRewiring` (in `CanonicalOriginRewiring`) : origin
  rewiring gives a canonical trifurcation

## iii. Table of contents

- A. Definitions
- B. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}

/-! ## A. Definitions -/

/-- Every configuration with three distinct infinite clusters meeting `B_n` has three sites whose
clusters after removing the origin are infinite and pairwise distinct. -/
def bc9_DistinctCutClusters (d n : ℕ) : Prop :=
  (∀ ω ∈ threeMeetBox d n,
      ∃ x₁ x₂ x₃ : Site d,
        (cluster d (removeSite 0 ω) x₁).Infinite ∧
        (cluster d (removeSite 0 ω) x₂).Infinite ∧
        (cluster d (removeSite 0 ω) x₃).Infinite ∧
        cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂ ∧
        cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃ ∧
        cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d),
      cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y →
        ∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x →
          ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) y →
            ¬ IsOpenEdge d (removeSite 0 ω) u v)

/-! ## B. Results -/

lemma bc9_distinctCutClusters (n : ℕ) : bc9_DistinctCutClusters d n :=
  ⟨fun ω hω => bc8_threeArmClusters_distinct n ω hω,
   fun _ω _x _y hne => bc7_cut_no_crossing hne⟩

lemma bc9_threeArms_pairwiseNoMerge (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hω : ω ∈ threeMeetBox d n) :
    ∃ x₁ x₂ x₃ : Site d,
      (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧
      (cluster d (removeSite 0 ω) x₃).Infinite ∧
      cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂ ∧
      cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃ ∧
      cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃ ∧
      Disjoint (cluster d (removeSite 0 ω) x₁) (cluster d (removeSite 0 ω) x₂) ∧
      Disjoint (cluster d (removeSite 0 ω) x₁) (cluster d (removeSite 0 ω) x₃) ∧
      Disjoint (cluster d (removeSite 0 ω) x₂) (cluster d (removeSite 0 ω) x₃) ∧
      (∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x₁ →
        ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) x₂ →
          ¬ IsOpenEdge d (removeSite 0 ω) u v) ∧
      (∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x₁ →
        ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) x₃ →
          ¬ IsOpenEdge d (removeSite 0 ω) u v) ∧
      (∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x₂ →
        ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) x₃ →
          ¬ IsOpenEdge d (removeSite 0 ω) u v) := by
  obtain ⟨x₁, x₂, x₃, hi1, hi2, hi3, hd12, hd13, hd23⟩ := bc8_threeArmClusters_distinct n ω hω
  exact ⟨x₁, x₂, x₃, hi1, hi2, hi3, hd12, hd13, hd23,
    bc8_disjoint_of_cut_ne hd12, bc8_disjoint_of_cut_ne hd13, bc8_disjoint_of_cut_ne hd23,
    bc7_cut_no_crossing hd12, bc7_cut_no_crossing hd13, bc7_cut_no_crossing hd23⟩

section AxiomAudit

/-- info: 'StatMech.Walls.bc9_distinctCutClusters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bc9_distinctCutClusters

/-- info: 'StatMech.Walls.bc9_threeArms_pairwiseNoMerge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bc9_threeArms_pairwiseNoMerge

end AxiomAudit

end Walls

end StatMech
