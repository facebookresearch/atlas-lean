/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.LatticeThreeExitTree

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.LatticeThreeExitTree`

* In `ℤ²` with the box `B_0 = {0}` and exits to `(1, 0)`, `(-1, 0)`, `(0, 1)`:
  `threeExitTip_degree_one` and `threeExitGraph_connected` hold, and `lattice_three_exit_tree`
  produces a tree joining the three exits through a hub (instance).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.LatticeThreeExitTree

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation

/-- The three exits `(1, 0)`, `(-1, 0)`, `(0, 1)` of the origin. -/
def out : Fin 3 → Site 2 := ![![1, 0], ![-1, 0], ![0, 1]]

/-- The origin lies in `B_0`. -/
theorem zero_mem : (0 : Site 2) ∈ box 2 0 := fun i => by simp

-- Each tip of the extended graph has degree one.
example (i : Fin 3) :
    (threeExitGraph (n := 0) fun _ => (0 : Site 2)).degree (threeExitTip i) = 1 :=
  threeExitTip_degree_one _ (fun _ => zero_mem) i

-- The extended graph is connected.
example : (threeExitGraph (n := 0) fun _ => (0 : Site 2)).Connected :=
  threeExitGraph_connected _ fun _ => zero_mem

-- A tree through a hub joining the three exits.
example : ∃ (C : Set (ThreeExitVertex 2 0)) (T : SimpleGraph C) (_ : DecidableRel T.Adj)
    (hub : C) (stem leaf : Fin 3 → C), T.IsTree ∧ Function.Injective stem ∧
    (∀ i, T.Adj hub (stem i)) ∧
    (∀ i j, i ≠ j → ¬ (T.deleteIncidenceSet hub).Reachable (leaf i) (leaf j)) := by
  obtain ⟨C, T, inst, hub, stem, leaf, hT, -, -, -, hsi, hha, -, -, -, -, -,
    hsep⟩ :=
    lattice_three_exit_tree (n := 0) (fun _ => (0 : Site 2)) out (fun _ => zero_mem)
      (fun i h => by
        have h0 := h 0
        have h1 := h 1
        fin_cases i <;> simp [out] at h0 h1)
      (by decide)
      (fun i => by fin_cases i <;> simp [out, Fin.sum_univ_two])
  exact ⟨C, T, inst, hub, stem, leaf, hT, hsi, hha, hsep⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.LatticeThreeExitTree
