/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.RowArcSeparatingSet

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.RowArcSeparatingSet`

* `jsi_cell` evaluates coordinatewise.
* A monotone arc of the whole plane in the one-row box `[0, 0] × [0, 0]`, and the lattice path
  `jsi_monotoneArc_walk` extracts from it.
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.RowArcSeparatingSet

example : jsi_cell 2 3 0 = 2 ∧ jsi_cell 2 3 1 = 3 := ⟨rfl, rfl⟩

/-- The constant column `0` is a monotone arc of `univ` in `[0, 0] × [0, 0]`. -/
def univArc : JsiMonotoneArc (Set.univ : Set (Site 2)) 0 0 0 0 where
  col := fun _ => 0
  band_lo := fun _ _ _ => le_rfl
  band_hi := fun _ _ _ => le_rfl
  shift := fun _ h1 h2 => by omega
  on_arc := fun _ _ _ _ _ _ => Set.mem_univ _
  cd := le_rfl
  shift_all := fun _ => Or.inr (Or.inl (sub_self 0))
  corner := fun _ _ _ _ _ _ => Set.mem_univ _

example : ∃ (n : ℕ) (W : (hypercubicLattice 2).Walk (jsi_cell (univArc.col 0) 0)
      (jsi_cell (univArc.col (0 + n)) (0 + n))),
    0 + (n : ℤ) = 0 ∧ (∀ z ∈ W.support, z ∈ (Set.univ : Set (Site 2))) :=
  jsi_monotoneArc_walk univArc

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.RowArcSeparatingSet
