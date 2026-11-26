/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneMerge
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RemoveForceCommute

/-!
# Cut clusters survive forcing

Forcing edges can only enlarge cut clusters, so infinite cut clusters stay infinite; forcing edges
at the origin does not change the cut configuration.

## i. Overview

Removing the origin after forcing `W` gives a configuration above `removeSite 0 ω`, so cut clusters
only grow and infinite cut clusters stay infinite. A site connected after forcing to a site with
infinite cut cluster has infinite cut cluster after forcing. If `W` avoids the origin, the origin
stays isolated. Forcing edges that contain the origin does not change the cut configuration, so cut
clusters are unchanged.

## ii. Key results

- `bc9_cutCluster_survives_infinite` : infinite cut clusters survive forcing.
- `StatMech.Walls.bc8_cluster_forceOpen_eq` (in `RemoveForceCommute`) : forcing at the origin leaves
  cut clusters unchanged.

## iii. Table of contents

- A. Monotonicity
- B. Forcing away from the origin
- C. Forcing at the origin

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

/-! ## A. Monotonicity -/

lemma bc9_removeSite_le_forceOpen
    (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSite (0 : Site d) ω ≤ removeSite (0 : Site d) (forceOpenFinset W ω) := by
  intro e
  by_cases h0 : (0 : Site d) ∈ e
  · rw [removeSite_apply_of_mem h0, removeSite_apply_of_mem h0]
  · rw [removeSite_apply_of_notMem h0, removeSite_apply_of_notMem h0]
    exact forceOpenFinset_le W ω e

lemma bc9_cutCluster_subset
    (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    cluster d (removeSite (0 : Site d) ω) x
      ⊆ cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x :=
  cluster_mono (bc9_removeSite_le_forceOpen W ω) x

lemma bc9_connected_of_base
    (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (h : Connected d (removeSite (0 : Site d) ω) x y) :
    Connected d (removeSite (0 : Site d) (forceOpenFinset W ω)) x y :=
  connected_mono (bc9_removeSite_le_forceOpen W ω) h

lemma bc9_cutCluster_survives_infinite
    (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (hinf : (cluster d (removeSite (0 : Site d) ω) x).Infinite) :
    (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x).Infinite :=
  hinf.mono (bc9_cutCluster_subset W ω x)

lemma bc9_reaches_shares_cluster
    (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (h : Connected d (removeSite (0 : Site d) (forceOpenFinset W ω)) x y) :
    cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x
      = cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y :=
  cluster_eq_of_connected h

lemma bc9_reaches_shares_infinite
    (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hinf : (cluster d (removeSite (0 : Site d) ω) x).Infinite)
    (h : Connected d (removeSite (0 : Site d) (forceOpenFinset W ω)) x y) :
    cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y
      = cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x ∧
      (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y).Infinite := by
  have heq := (bc9_reaches_shares_cluster W ω h).symm
  exact ⟨heq, heq ▸ bc9_cutCluster_survives_infinite W ω hinf⟩

/-! ## B. Forcing away from the origin -/

lemma bc9_cut_survives
    (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (_hW : ∀ e ∈ W, (0 : Site d) ∉ e) {x : Site d}
    (hinf : (cluster d (removeSite (0 : Site d) ω) x).Infinite) :
    (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x).Infinite ∧
    ∀ y, Connected d (removeSite (0 : Site d) (forceOpenFinset W ω)) x y →
      cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y
        = cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) x ∧
      (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y).Infinite :=
  ⟨bc9_cutCluster_survives_infinite W ω hinf,
   fun _y h => bc9_reaches_shares_infinite W ω hinf h⟩

lemma bc9_origin_isolated_of_avoiding
    (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (_hW : ∀ e ∈ W, (0 : Site d) ∉ e) (v : Site d) :
    ¬ (openSubgraph d (removeSite (0 : Site d) (forceOpenFinset W ω))).Adj 0 v := by
  rw [openSubgraph_adj]
  rintro ⟨_hadj, hopen⟩
  have h0mem : (0 : Site d) ∈ s((0 : Site d), v) := Sym2.mem_mk_left 0 v
  rw [removeSite_apply_of_mem h0mem] at hopen
  exact absurd hopen (by simp)

lemma bc9_cut_survives_self
    (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d)))
    (hW : ∀ e ∈ W, (0 : Site d) ∉ e)
    (hinf : (cluster d (removeSite (0 : Site d) ω) 0).Infinite) :
    (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) 0).Infinite ∧
    ∀ y, Connected d (removeSite (0 : Site d) (forceOpenFinset W ω)) 0 y →
      cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y
        = cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) 0 ∧
      (cluster d (removeSite (0 : Site d) (forceOpenFinset W ω)) y).Infinite :=
  bc9_cut_survives W ω hW hinf

/-! ## C. Forcing at the origin -/

end Walls

end StatMech
