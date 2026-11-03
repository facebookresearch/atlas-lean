/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalForestLeafCount

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalForestLeafCount`

* `bc69_globalForest_of_noTrif` builds `bc69_Gn_globalForest` in the all-closed configuration of
  `ℤ`, which has no contracted-lattice trifurcation (non-vacuity), and
  `bc69_coarseTcount_le_boundary` gives the coarse counting bound there.
* The second conjunct of `bc69_status`: the subtype coercion is injective (instance).
* The third conjunct as a conditional statement.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalForestLeafCount

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

/-- The site `1` of `ℤ` lies on the boundary of `B_1`. -/
theorem one_mem_vertexBoundary : (fun _ => 1 : Site 1) ∈ vertexBoundary 1 1 :=
  ⟨fun _ => le_rfl, fun h => by simpa using h 0⟩

/-- The site `-1` of `ℤ` lies on the boundary of `B_1`. -/
theorem neg_one_mem_vertexBoundary : (fun _ => -1 : Site 1) ∈ vertexBoundary 1 1 :=
  ⟨fun _ => by simp, fun h => by simpa using h 0⟩

/-- The two boundary sites `1` and `-1` of `B_1 ⊂ ℤ` are distinct. -/
theorem one_ne_neg_one : (fun _ => 1 : Site 1) ≠ fun _ => -1 := fun h => by
  simpa using congrFun h 0

/-- Every cluster of the all-closed configuration is finite. -/
theorem cluster_closed_finite {d : ℕ} (a : Site d) : (cluster d (fun _ => false) a).Finite := by
  have hb : openSubgraph d (fun _ => false) = ⊥ := by ext; simp
  have hc : cluster d (fun _ => false) a = {a} := by
    ext y
    simp [cluster, Connected, hb, eq_comm]
  exact hc ▸ Set.finite_singleton a

/-- Removing sites from the all-closed configuration changes nothing. -/
theorem removeSites_closed {d : ℕ} (T : Finset (Site d)) :
    removeSites T (fun _ => false) = fun _ => false :=
  funext fun e => by unfold removeSites; split_ifs <;> rfl

/-- The all-closed configuration has no contracted-lattice trifurcation. -/
theorem not_gnTrif_closed {d L : ℕ} (y : Site d) :
    ¬ bc67_IsGnTrifurcation (d := d) (fun _ => false) L y := by
  rintro ⟨a₁, -, -, -, ⟨h, -, -⟩, -⟩
  rw [removeSites_closed] at h
  exact h (cluster_closed_finite a₁)

/-- The global contracted forest in the all-closed configuration of `ℤ`. -/
theorem closed_globalForest (L : ℕ) : bc69_Gn_globalForest (d := 1) (fun _ => false) L 1 :=
  bc69_globalForest_of_noTrif _ L 1 one_mem_vertexBoundary neg_one_mem_vertexBoundary
    one_ne_neg_one fun y _ => not_gnTrif_closed y

-- The coarse counting bound in the all-closed configuration.
example : bc61_coarseTcount (d := 1) (fun _ => false) 2 1 ≤ boxSV_boundaryCard 1 1 :=
  bc69_coarseTcount_le_boundary _ 2 1 (closed_globalForest 2)

-- The coercion from the box is injective on any set.
example : Set.InjOn (Subtype.val : (↑(box 2 3) : Type) → Site 2) Set.univ :=
  (bc69_status (d := 2)).2.1 3 Set.univ

-- A global forest bounds the coarse count.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (h : bc69_Gn_globalForest ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R :=
  (bc69_status (d := 2)).2.2 ω L R h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalForestLeafCount
