/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalStarForest

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalStarForest`

* `bc70_spanningForest_acyclic` on the upper-lines configuration (instance).
* The third conjunct of `bc70_status` on the all-closed configuration of `ℤ`, whose forest
  structure comes from `bc69_globalForest_of_noTrif` (non-vacuity).
* `bc70_globalForest_of_singleStar` as a conditional statement.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalStarForest

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

-- The box spanning forest of the upper-lines configuration is acyclic.
example : (bc70_spanningForest bc60_upperLines 3).IsAcyclic :=
  bc70_spanningForest_acyclic _ 3

-- The coarse counting bound from the forest structure in the all-closed configuration.
example : bc61_coarseTcount (d := 1) (fun _ => false) 2 1 ≤ boxSV_boundaryCard 1 1 :=
  (bc70_status (d := 1)).2.2 _ 2 1
    (bc69_globalForest_of_noTrif _ 2 1 one_mem_vertexBoundary neg_one_mem_vertexBoundary
      one_ne_neg_one fun y _ => not_gnTrif_closed y)

-- One trifurcation with three distinct boundary ends gives a global forest.
example (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (x : Site 2) (a : Fin 3 → Site 2)
    (hx : x ∈ box 2 R) (ht : bc67_IsGnTrifurcation ω L x)
    (hs : ∀ y, y ∈ box 2 R → bc67_IsGnTrifurcation ω L y → y = x)
    (hb : ∀ i, a i ∈ vertexBoundary 2 R) (hne : ∀ i, a i ≠ x) (hinj : Function.Injective a) :
    bc69_Gn_globalForest ω L R :=
  bc70_globalForest_of_singleStar ω L R a hx ht hs hb hne hinj

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalStarForest
