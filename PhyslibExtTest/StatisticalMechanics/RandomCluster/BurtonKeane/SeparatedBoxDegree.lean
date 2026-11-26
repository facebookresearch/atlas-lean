/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SeparatedBoxDegree

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SeparatedBoxDegree`

* the all-closed configuration has no separated coarse trifurcation (`bc106_SeparatedCoarseTrif`);
* instance: the last conjunct of `bsd_status` at `L = 1` (disjoint boxes around `0` and `(3, 0)`,
  and a connection in `bc60_upperLines`);
* `bsd_deg3_free_per_trif` and the box-disjointness conjunct of `bsd_status` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SeparatedBoxDegree

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

variable {d : ℕ}

/-- In the all-closed configuration every open cluster is a single site. -/
theorem cluster_closed (x : Site d) : cluster d (fun _ => false) x = {x} := by
  have hbot : openSubgraph d (fun _ => false) = ⊥ := by
    ext a b
    simp
  ext y
  simp only [mem_cluster, Connected, hbot, SimpleGraph.reachable_bot, Set.mem_singleton_iff]
  exact eq_comm

/-- In the all-closed configuration no site is a trifurcation. -/
theorem not_isTrifurcation_closed (x : Site d) :
    ¬ IsTrifurcation d (fun _ => false) x := by
  rintro ⟨a₁, -, -, -, -, ⟨h, -, -⟩, -⟩
  rw [cluster_closed] at h
  exact h (Set.finite_singleton a₁)

/-- Removing sites from the all-closed configuration leaves it all-closed. -/
theorem removeSites_closed (T : Finset (Site d)) :
    removeSites T (fun _ => false) = fun _ => false := by
  funext e
  simp only [removeSites, ite_self]

/-- The all-closed configuration has no contracted-lattice trifurcation. -/
theorem not_gnTrif_closed (L : ℕ) (y : Site d) : ¬ bc67_IsGnTrifurcation (fun _ => false) L y := by
  rintro ⟨a, -, -, -, ⟨h, -, -⟩, -⟩
  rw [removeSites_closed, cluster_closed] at h
  exact h (Set.finite_singleton a)

/-- The all-closed configuration has no coarse trifurcation. -/
theorem not_coarseTrif_closed (L : ℕ) (y : Site d) :
    ¬ bc61_IsCoarseTrifurcation (fun _ => false) L y := by
  rintro ⟨a, -, -, -, -, -, ⟨h, -, -⟩, -⟩
  rw [removeSites_closed, cluster_closed] at h
  exact h (Set.finite_singleton a)


-- Separated coarse trifurcations are coarse, so the all-closed configuration has none.
example (L : ℕ) (y : Site d) : ¬ bc106_SeparatedCoarseTrif (fun _ => false) L y :=
  fun h => not_coarseTrif_closed L y (bc106_isCoarseTrif_of_separated h)

-- The planar witness at `L = 1`.
example : Disjoint (bc61_boxAround 2 1 (0 : Site 2))
      (bc61_boxAround 2 1 (bc57_pt (2 * 1 + 1) 0)) ∧
    Connected 2 bc60_upperLines (bc57_pt (1 + 1) 1) (bc57_pt (2 * 1 + 1 + (1 + 1)) 1) := by
  exact_mod_cast (bsd_status (d := 2)).2.2.2 1

-- Boxes of distinct separated coarse trifurcations are disjoint.
example (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x y : Site d)
    (hx : bc106_SeparatedCoarseTrif ω L x) (hy : bc106_SeparatedCoarseTrif ω L y) (hxy : x ≠ y) :
    Disjoint (bc61_boxAround d L x) (bc61_boxAround d L y) :=
  bsd_status.1 ω L x y hx hy hxy

-- A separated coarse trifurcation has degree at least three after collapsing its box.
example (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x : Site d)
    (hx : bc106_SeparatedCoarseTrif ω L x) :
    ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (hyS : x ∈ S)
      (_ : DecidableRel ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L x)).induce S).Adj),
      3 ≤ ((bc72_quotGraph (openSubgraph d ω) (bc72_collapseBox L x)).induce S).degree ⟨x, hyS⟩ :=
  bsd_deg3_free_per_trif hx

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.SeparatedBoxDegree
