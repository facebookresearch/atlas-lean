/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifExploration

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifExploration`

* non-vacuity: `bge_ArmComponents` holds for the all-closed configuration (no classical coarse
  trifurcation), and `bge_exploration_of_armComponents` gives `bfg_GenuineExploration` for it in
  `ℤ²` at `R = 1`;
* `bge_singleGenuineTrif_arms_disjoint` on the all-closed configuration: clusters of distinct sites
  after removing a box are disjoint;
* `bge_exploration_of_singleGenuineTrif` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TrifExploration

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open _root_.StatMech.ConfigSpace MeasureTheory

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

/-- The two boundary sites `(1, 0)` and `(1, 1)` of `B_1` in `ℤ²`. -/
def b₁ : Site 2 := ![1, 0]

/-- See `b₁`. -/
def b₂ : Site 2 := ![1, 1]

/-- `b₁` lies on the boundary of `B_1`. -/
theorem b₁_mem : b₁ ∈ vertexBoundary 2 1 := by
  simp only [mem_vertexBoundary, mem_box, b₁, Fin.forall_fin_two]
  decide

/-- `b₂` lies on the boundary of `B_1`. -/
theorem b₂_mem : b₂ ∈ vertexBoundary 2 1 := by
  simp only [mem_vertexBoundary, mem_box, b₂, Fin.forall_fin_two]
  decide

/-- The two boundary sites differ. -/
theorem b₁_ne_b₂ : b₁ ≠ b₂ := fun h => by simpa [b₁, b₂] using congrFun h 1
/-- The all-closed configuration has no classical coarse trifurcation. -/
theorem not_genuine_closed (L : ℕ) (y : Site d) :
    ¬ btr_IsGenuineCoarseTrif (fun _ => false) L y := by
  rintro ⟨a, -, -, ⟨b, -, hb⟩, -⟩
  exact Bool.false_ne_true hb.2

open Classical in
/-- Hence its set of classical coarse trifurcations is empty. -/
theorem genuineFinset_closed (L R : ℕ) :
    btr_genuineTrifFinset (d := d) (fun _ => false) L R = ∅ := by
  rw [btr_genuineTrifFinset, Finset.filter_eq_empty_iff]
  exact fun y _ => not_genuine_closed L y

/-- The all-closed configuration has arm components (there is nothing to cover). -/
theorem closed_arms (L R : ℕ) : bge_ArmComponents (d := d) (fun _ => false) L R :=
  ⟨fun _ => ∅, fun p => absurd p.1.2 (by simp [genuineFinset_closed]),
    fun p => absurd p.1.2 (by simp [genuineFinset_closed])⟩

-- Arm components give an exploration certificate.
example (L : ℕ) : bfg_GenuineExploration (d := 2) (fun _ => false) L 1 :=
  bge_exploration_of_armComponents _ L 1 b₁_mem b₂_mem b₁_ne_b₂ (closed_arms L 1)

-- Clusters of distinct sites after removing a box are disjoint in the all-closed configuration.
example (L : ℕ) (y a₁ a₂ a₃ : Site d) (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h23 : a₂ ≠ a₃) :
    Disjoint (cluster d (removeSites (bc61_boxAround d L y) (fun _ => false)) a₁)
      (cluster d (removeSites (bc61_boxAround d L y) (fun _ => false)) a₂) := by
  refine (bge_singleGenuineTrif_arms_disjoint (a₃ := a₃) ⟨?_, ?_, ?_⟩).1 <;>
    rw [removeSites_closed, ← mem_cluster, cluster_closed] <;> simpa [eq_comm]

-- A single classical coarse trifurcation whose arms reach the boundary gives an exploration.
example (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (y : Site d)
    (hy : btr_IsGenuineCoarseTrif ω L y)
    (huniq : ∀ z, z ∈ box d R → btr_IsGenuineCoarseTrif ω L z → z = y)
    (hbdry : ∀ a : Site d, (∃ b ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b a) →
      Connected d ω y a → (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite →
      (cluster d (removeSites (bc61_boxAround d L y) ω) a ∩ vertexBoundary d R).Nonempty) :
    bfg_GenuineExploration ω L R :=
  bge_exploration_of_singleGenuineTrif ω L R y hy huniq hbdry

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TrifExploration
