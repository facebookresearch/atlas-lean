/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.InfiniteClusterTail

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.InfiniteClusterTail`

* In `ℤ` with every edge open, the cluster of the origin is infinite; minus `{0}` it has an
  infinite component (`infiniteCluster_component_after_finset`), and
  `infiniteCluster_has_open_exit_to_infinite_tail` gives an open exit edge from `{0}` into an
  infinite tail; `infiniteClusterTailData` packages it (instance).
* `threeInfiniteClusters_have_disjoint_tails` as a conditional statement.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.InfiniteClusterTail

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

/-- In `ℤ` with every edge open, the origin is connected to every `n ∈ ℕ`. -/
theorem conn_nat (n : ℕ) : Connected 1 (fun _ => true) 0 (fun _ => (n : ℤ)) := by
  induction n with
  | zero =>
    have h : (fun _ : Fin 1 => ((0 : ℕ) : ℤ)) = 0 := by funext; simp
    rw [h]
  | succ n ih => exact ih.trans (IsOpenEdge.connected ⟨by simp, rfl⟩)

/-- In `ℤ` with every edge open, the cluster of the origin is infinite. -/
theorem open_origin_infinite : (cluster 1 (fun _ => true) 0).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (fun _ => (n : ℤ) : Site 1))
    (fun a b h => by simpa using congrFun h 0) conn_nat

-- Removing the origin leaves an infinite component.
example : ∃ D : (tailClusterGraph (d := 1) (fun _ => true) 0).ComponentCompl
    (↑(tailClusterCut (d := 1) (fun _ => true) 0 {0})), D.supp.Infinite :=
  infiniteCluster_component_after_finset _ 0 open_origin_infinite {0}

-- An open exit edge from `{0}` into an infinite tail of the cluster.
example : ∃ u v : Site 1, ∃ T : Set (Site 1), u ∈ ({0} : Finset (Site 1)) ∧
    v ∉ ({0} : Finset (Site 1)) ∧ (openSubgraph 1 fun _ => true).Adj u v ∧ v ∈ T ∧
    T.Infinite ∧ T ⊆ cluster 1 (fun _ => true) 0 ∧
    (∀ a ∈ T, ∀ b ∈ T, ∃ (ha : a ∉ ((({0} : Finset (Site 1))) : Set (Site 1)))
      (hb : b ∉ ((({0} : Finset (Site 1))) : Set (Site 1))),
      ((openSubgraph 1 fun _ => true).induce
        ((({0} : Finset (Site 1))) : Set (Site 1))ᶜ).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :=
  infiniteCluster_has_open_exit_to_infinite_tail _ 0 open_origin_infinite {0} (by simp)

-- The packaged tail data: its tail is infinite and lies in the cluster.
example : (infiniteClusterTailData (d := 1) (fun _ => true) 0 open_origin_infinite {0}
    (by simp)).tail.Infinite :=
  (infiniteClusterTailData _ 0 open_origin_infinite {0} (by simp)).tail_infinite

-- Three distinct infinite clusters have pairwise disjoint tails.
example (ω : ConfigSpace (Sym2 (Site 2))) (K : Finset (Site 2)) (x1 x2 x3 : Site 2)
    (h1 : x1 ∈ K) (h2 : x2 ∈ K) (h3 : x3 ∈ K) (hi1 : (cluster 2 ω x1).Infinite)
    (hi2 : (cluster 2 ω x2).Infinite) (hi3 : (cluster 2 ω x3).Infinite)
    (h12 : cluster 2 ω x1 ≠ cluster 2 ω x2) (h13 : cluster 2 ω x1 ≠ cluster 2 ω x3)
    (h23 : cluster 2 ω x2 ≠ cluster 2 ω x3) :
    ∃ D1 : InfiniteClusterTailData ω K x1, ∃ D2 : InfiniteClusterTailData ω K x2,
      ∃ D3 : InfiniteClusterTailData ω K x3,
        Disjoint D1.tail D2.tail ∧ Disjoint D1.tail D3.tail ∧ Disjoint D2.tail D3.tail :=
  threeInfiniteClusters_have_disjoint_tails ω K x1 x2 x3 h1 h2 h3 hi1 hi2 hi3 h12 h13 h23

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.InfiniteClusterTail
