/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.Filter.Defs
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalForestData
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmRay
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SeparatedTrifContraction
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseStarForestEmbedding

/-!
# Degree three at separated coarse trifurcations

A separated coarse trifurcation has degree at least three after its box is collapsed, and a single
separated trifurcation gives a global contracted forest.

## i. Overview

Separated coarse trifurcations (`bc106_SeparatedCoarseTrif`) have disjoint boxes. Collapsing the box
of one of them gives a vertex of degree at least three in a finite induced subgraph of the quotient
graph. If it is the only contracted-lattice trifurcation in `B_R` and its three arms stay infinite,
a star gives `bc69_Gn_globalForest`. The global forest for every configuration gives uniqueness for
Bernoulli percolation.

The trifurcation notion here is the coarse one on `L`-boxes (`bc61_IsCoarseTrifurcation`,
`bc67_IsGnTrifurcation`), whose arms are infinite after the whole `L`-box is removed. Results that
assume a certificate for every configuration are conditional: no such certificate is constructed for
all configurations.

## ii. Key results

- `bsd_deg3_free_per_trif` : degree three after collapsing the box
- `bsd_bc69_of_separated_singleStar_route` : a single separated trifurcation gives the global forest
- `bsd_status` : the statements together

## iii. Table of contents

- A. Results
- B. Summary

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Results -/

lemma bsd_deg3_free_per_trif {L : ℕ} {x : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (hx : bc106_SeparatedCoarseTrif ω L x) :
    ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : x ∈ S)
      (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L x)).induce S).Adj),
      3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L x)).induce S).degree ⟨x, hyS⟩ :=
  bc72_quot_deg3_of_gnTrif (bc106_gnTrif_of_separated hx)

lemma bsd_arm_tips_of_separated (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    {x : Site d} (arm : Fin 3 → Site d)
    (harmbox : ∀ i, arm i ∈ box d R)
    (harmne : ∀ i, arm i ≠ x)
    (harminf : ∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite)
    (harmsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j)) :
    ∃ t : Fin 3 → Site d,
      (∀ i, t i ∈ vertexBoundary d R) ∧
      (∀ i, (bc67_contractedLattice ω L x).Reachable (arm i) (t i)) ∧
      (∀ i, t i ≠ x) ∧
      (∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (t i) (t j)) := by
  classical
  have htip : ∀ i, ∃ t, (bc67_contractedLattice ω L x).Reachable (arm i) t ∧
      t ∈ vertexBoundary d R := by
    intro i
    obtain ⟨r, hr0, hinj, hadjr, hreachr⟩ :=
      bar_armRay_of_infiniteComponent ω L x (arm i) (harminf i)
    have hlat : ∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1)) := fun k =>
      ((bc67_contractedLattice_le ω L x) (hadjr k)).1
    have h0box : r 0 ∈ box d R := by rw [hr0]; exact harmbox i
    obtain ⟨k, hk⟩ := bar_ray_crosses_boundary r hinj hlat R hR h0box
    exact ⟨r k, hreachr k, hk⟩
  choose tip htipreach htipbdry using htip
  refine ⟨tip, htipbdry, htipreach, ?_, ?_⟩
  · intro i hti
    have hr := htipreach i
    rw [hti] at hr
    exact harmne i (bar_center_reach_eq ω L hr.symm)
  · intro i j hij
    exact bar_armSep_of_rays ω L x (htipreach i) (htipreach j) (harmsep i j hij)

lemma bsd_bc69_of_separated_singleStar_route (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    {x : Site d} (arm : Fin 3 → Site d)
    (hxbox : x ∈ box d R)
    (hxsep : bc106_SeparatedCoarseTrif ω L x)
    (hsingle : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x)
    (harmbox : ∀ i, arm i ∈ box d R)
    (harmne : ∀ i, arm i ≠ x)
    (harminf : ∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite)
    (harmsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j))
    (hroute : ∀ a : Fin 3 → Site d,
      (∀ i, (bc67_contractedLattice ω L x).Reachable (arm i) (a i)) →
      (∀ i, a i ∈ vertexBoundary d R) →
      ∀ i j, i ≠ j → (bc67_contractedLattice ω L (a j)).Reachable x (a i)) :
    bc69_Gn_globalForest ω L R :=
  bgc_globalForest_of_trifForestData ω L R
    (bar_trifForestData_of_arms_route ω L R hR arm hxbox
      (bc106_gnTrif_of_separated hxsep) hsingle harmbox harmne harminf harmsep hroute)

/-! ## B. Summary -/

lemma bsd_status :
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x y : Site d),
      bc106_SeparatedCoarseTrif ω L x → bc106_SeparatedCoarseTrif ω L y → x ≠ y →
      Disjoint (bc61_boxAround d L x) (bc61_boxAround d L y)) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x : Site d),
      bc106_SeparatedCoarseTrif ω L x →
      ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : x ∈ S)
        (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L x)).induce S).Adj),
        3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L x)).induce S).degree ⟨x, hyS⟩) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (x : Site d) (arm : Fin 3 → Site d),
      x ∈ box d R → bc106_SeparatedCoarseTrif ω L x →
      (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x) →
      (∀ i, arm i ∈ box d R) → (∀ i, arm i ≠ x) →
      (∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite) →
      (∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j)) →
      (∀ a : Fin 3 → Site d,
        (∀ i, (bc67_contractedLattice ω L x).Reachable (arm i) (a i)) →
        (∀ i, a i ∈ vertexBoundary d R) →
        ∀ i j, i ≠ j → (bc67_contractedLattice ω L (a j)).Reachable x (a i)) →
      bc69_Gn_globalForest ω L R) ∧
    (∀ (L : ℕ),
      Disjoint (bc61_boxAround 2 L (0 : Site 2))
          (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧
        Connected 2 bc60_upperLines
          (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L x y hx hy hne; exact bc106_boxes_disjoint hx hy hne
  · intro ω L x hx; exact bsd_deg3_free_per_trif hx
  · intro ω L R hR x arm hxbox hxsep hsingle harmbox harmne harminf harmsep hroute
    exact bsd_bc69_of_separated_singleStar_route ω L R hR arm hxbox hxsep hsingle
      harmbox harmne harminf harmsep hroute
  · intro L; exact bc64_arms_can_share_boundary L

end StatMech.Walls
