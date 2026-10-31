/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.StarForestFiber

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.StarForestFiber`

* `bct_fiberForest_acyclic` and `bct_fiberForest_degree` on two copies of the double star
  `bct_dstarG` (a hub keeps degree `3`);
* the double star itself: `bct_dstarG_isTree`, hub and leaf degrees;
* non-vacuity: `bct_exploration_of_carrier` builds `bfg_GenuineExploration` for the all-closed
  configuration of `ℤ²` at `R = 1` from the path on `Fin 2` with leaf components `{(1, 0)}` and
  `{(1, 1)}`, and `bct_genuineTcount_of_carrier` gives the classical coarse count.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.StarForestFiber

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open _root_.StatMech.ConfigSpace MeasureTheory

variable {d : ℕ}

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

-- Two copies of the double star form a forest in which hubs keep degree three.
example : (bct_fiberForest (Fin 2) (Fin 6) bct_dstarG).IsAcyclic ∧
    (bct_fiberForest (Fin 2) (Fin 6) bct_dstarG).degree (1, 0) = 3 := by
  refine ⟨bct_fiberForest_acyclic _ _ _ bct_dstarG_isAcyclic, ?_⟩
  rw [bct_fiberForest_degree, bct_dstarG_hub0_deg]

-- The double star is a tree with two hubs and four leaves.
example : bct_dstarG.IsTree ∧ bct_dstarG.degree 1 = 3 ∧ bct_dstarG.degree 5 = 1 :=
  ⟨bct_dstarG_isTree, bct_dstarG_hub1_deg, bct_dstarG_leaf_deg 5 (by decide) (by decide)⟩

/-- The two leaf components. -/
def comp (v : Fin 2) : Set (Site 2) := if v = 0 then {b₁} else {b₂}

/-- Every vertex of the path on `Fin 2` has degree one. -/
theorem path_deg (v : Fin 2) : (SimpleGraph.pathGraph 2).degree v = 1 := by
  fin_cases v <;> decide

/-- The leaf components meet the boundary. -/
theorem comp_bnd (v : Fin 2) : (comp v ∩ vertexBoundary 2 1).Nonempty := by
  fin_cases v
  · exact ⟨b₁, by simp [comp], b₁_mem⟩
  · exact ⟨b₂, by simp [comp], b₂_mem⟩

/-- The leaf components are disjoint. -/
theorem comp_disj (u v : Fin 2) (huv : u ≠ v) : Disjoint (comp u) (comp v) := by
  fin_cases u <;> fin_cases v <;> simp_all [comp, b₁_ne_b₂, b₁_ne_b₂.symm]

-- The carrier gives an exploration certificate for the all-closed configuration.
example (L : ℕ) : bfg_GenuineExploration (d := 2) (fun _ => false) L 1 :=
  bct_exploration_of_carrier _ L 1 (Fin 2) (SimpleGraph.pathGraph 2) (fun _ => 0) comp
    (SimpleGraph.isTree_pathGraph_add_one 1).isAcyclic (fun v => (path_deg v).ge)
    (fun y _ h => absurd h (not_genuine_closed L y))
    (fun y _ h => absurd h (not_genuine_closed L y))
    (fun v _ => comp_bnd v) (fun u _ v _ huv => comp_disj u v huv)

-- And the classical coarse count.
example (L : ℕ) :
    (btr_genuineTrifFinset (d := 2) (fun _ => false) L 1).card ≤ boxSV_boundaryCard 2 1 :=
  bct_genuineTcount_of_carrier _ L 1 (Fin 2) (SimpleGraph.pathGraph 2) (fun _ => 0) comp
    (SimpleGraph.isTree_pathGraph_add_one 1).isAcyclic (fun v => (path_deg v).ge)
    (fun y _ h => absurd h (not_genuine_closed L y))
    (fun y _ h => absurd h (not_genuine_closed L y))
    (fun v _ => comp_bnd v) (fun u _ v _ huv => comp_disj u v huv)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.StarForestFiber
