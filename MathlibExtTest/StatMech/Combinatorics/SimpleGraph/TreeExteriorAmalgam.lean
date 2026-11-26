/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.TreeExteriorAmalgam
public import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.TreeExteriorAmalgam`

* `tree_exterior_amalgam_separated` is non-vacuous: take the star graph on `Fin 4` with hub `0`
  and leaves `1, 2, 3`, the identity embedding, the empty exterior graph `E = ⊥` and `U = T`.
  All hypotheses are discharged and the conclusion is derived.
-/

@[expose] public section

open SimpleGraph StatMech.Percolation

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.TreeExteriorAmalgam

/-- The three leaves `1, 2, 3` of the star graph on `Fin 4`. -/
def leaf : Fin 3 → Fin 4 := fun i => i.succ

theorem leaf_injective : Function.Injective leaf := Fin.succ_injective 3

/-- Leaves are separated in the star graph once the edges at the centre are deleted. -/
theorem hcut : ∀ i j, i ≠ j →
    ¬ ((starGraph (0 : Fin 4)).deleteIncidenceSet 0).Reachable (leaf i) (leaf j) := by
  intro i j hij
  have hne : leaf i ≠ leaf j := fun h => hij (leaf_injective h)
  exact StatMech.Percolation.ftt_neighbors_separated _ (isAcyclic_starGraph 0)
    (by simpa [leaf] using (Fin.succ_ne_zero i).symm)
    (by simpa [leaf] using (Fin.succ_ne_zero j).symm) hne

/-- The amalgamation theorem for the star tree with an empty exterior graph. -/
example : ∀ i j, i ≠ j →
    ¬ ((starGraph (0 : Fin 4)).deleteIncidenceSet (id 0)).Reachable (id (leaf i)) (id (leaf j)) :=
  tree_exterior_amalgam_separated (starGraph (0 : Fin 4)) (⊥ : SimpleGraph (Fin 4))
    (starGraph (0 : Fin 4)) id Function.injective_id 0 leaf hcut
    (fun i j hij h => by
      rw [reachable_bot] at h
      exact hij (leaf_injective h))
    (fun _ _ h => h.elim)
    (fun {x y} h => Or.inr ⟨x, y, h, rfl, rfl⟩)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.TreeExteriorAmalgam
