/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.StarArmUnion

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.StarArmUnion`

* instance: for the three-arm star `bgf3_starRay`/`bgf3_starLen` on `Fin 4` the hub `0` has degree
  at least `3` in the arm-union graph (`bgf3_deg3`);
* `bgf3_acyclic`: a single arm along the path on `Fin 2` spans an acyclic graph;
* the counting conjunct of `bgf3_status`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.StarArmUnion

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open _root_.StatMech.ConfigSpace MeasureTheory

/-- Each star arm is injective on `{0, 1}`. -/
theorem star_inj (α : Fin 3) : Set.InjOn (bgf3_starRay α) {n | n ≤ bgf3_starLen α} := by
  intro a ha b hb hab
  simp only [bgf3_starLen, Set.mem_ofPred_eq] at ha hb
  interval_cases a <;> interval_cases b <;> fin_cases α <;> simp_all [bgf3_starRay]

open Classical in
-- The hub of the star has degree at least three in the union of its arms.
example : 3 ≤ (bgf3_G bgf3_starRay bgf3_starLen).degree 0 :=
  bgf3_deg3 (f := fun _ : Unit => (0 : Fin 4)) (arm3 := fun _ j => j) bgf3_starRay bgf3_starLen
    (fun _ => le_rfl) star_inj (fun _ j => by simp [bgf3_starRay]) (by decide) ()

-- A single arm of length one along the path on `Fin 2` spans an acyclic graph.
example :
    (bgf3_G (fun (_ : Unit) (n : ℕ) => (if n = 0 then 0 else 1 : Fin 2)) (fun _ => 1)).IsAcyclic :=
  bgf3_acyclic _ _ (SimpleGraph.isTree_pathGraph_add_one 1) fun _ k hk => by
    interval_cases k
    simp [SimpleGraph.pathGraph_adj]

-- One hub, three boundary leaves.
example : Fintype.card (Fin 1) ≤ ({1, 2, 3} : Finset (Fin 4)).card := bgf3_status.2.2

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.StarArmUnion
