/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineExplorationLeaf

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineExplorationLeaf`

* `bfg_leafSel_injOn` on two disjoint singleton components meeting the boundary of `B_1 ⊂ ℤ`
  (instance).
* The fourth conjunct of `bfg_status` builds `bfg_GenuineExploration` in the all-closed
  configuration, which has no classical coarse trifurcation (non-vacuity); then
  `bfg_genuineForest_of_exploration` and `bfg_genuineTcount_le_boundary` apply to it.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineExplorationLeaf

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

/-- The all-closed configuration has no classical coarse trifurcation: no edge leaves a box. -/
theorem not_genuineCoarseTrif_closed {d L : ℕ} (y : Site d) :
    ¬ btr_IsGenuineCoarseTrif (d := d) (fun _ => false) L y := by
  rintro ⟨a₁, -, -, ⟨b, -, hb⟩, -⟩
  simp at hb

-- Leaf selection is injective on two disjoint components meeting the boundary.
example : Set.InjOn (bfg_leafSel (fun b : Bool => if b then {(fun _ => 1 : Site 1)}
    else {(fun _ => -1 : Site 1)}) 1) Set.univ :=
  bfg_leafSel_injOn _ 1
    (fun v _ => by
      cases v
      · exact ⟨_, rfl, neg_one_mem_vertexBoundary⟩
      · exact ⟨_, rfl, one_mem_vertexBoundary⟩)
    (fun u _ v _ huv => by
      cases u <;> cases v <;> simp_all [one_ne_neg_one, eq_comm])

/-- The exploration certificate holds in the all-closed configuration of `ℤ`. -/
theorem closed_exploration (L : ℕ) : bfg_GenuineExploration (d := 1) (fun _ => false) L 1 :=
  (bfg_status (d := 1)).2.2.2 _ L 1 _ _ one_mem_vertexBoundary neg_one_mem_vertexBoundary
    one_ne_neg_one fun y _ => not_genuineCoarseTrif_closed y

-- The exploration gives the classical coarse forest and the counting bound.
example : bgt_GenuineForest (d := 1) (fun _ => false) 2 1 ∧
    (btr_genuineTrifFinset (d := 1) (fun _ => false) 2 1).card ≤ boxSV_boundaryCard 1 1 :=
  ⟨bfg_genuineForest_of_exploration _ 2 1 (closed_exploration 2),
    bfg_genuineTcount_le_boundary _ 2 1 (closed_exploration 2)⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineExplorationLeaf
