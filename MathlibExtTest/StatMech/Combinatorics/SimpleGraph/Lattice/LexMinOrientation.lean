/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.LexMinOrientation

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.LexMinOrientation`

* `lmo_lexMinCell` at the unit cell and at the domino.
* The named predicate `lmo_OrbitReachesLeftmost` holds for the unit cell.
* `lmo_windingWitness_of_reachesLeftmost` is instantiated at the unit cell (cycle hypothesis
  proved from `shw_unitCell_faceInj`).
* `lmo_lexKey` at a small site.
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.LexMinOrientation

/-- The face loop of the unit cell is a cycle. -/
theorem unitCell_loop_isCycle : (mpl_orbitLoop unitCell ucBase).IsCycle :=
  mpl_orbitLoop_isCycle unitCell ucBase (by rw [unitCell_orbitPeriod_eq_four]; norm_num)
    shw_unitCell_faceInj

example : ∃ z₀ ∈ unitCell, (![z₀ 0 - 1, z₀ 1] : Site 2) ∉ unitCell ∧
    (![z₀ 0, z₀ 1 - 1] : Site 2) ∉ unitCell ∧ (∀ w ∈ unitCell, z₀ 0 ≤ w 0) :=
  lmo_lexMinCell unitCell unitCell_finite (Set.singleton_nonempty _)

example : ∃ z₀ ∈ domino, (![z₀ 0 - 1, z₀ 1] : Site 2) ∉ domino ∧
    (![z₀ 0, z₀ 1 - 1] : Site 2) ∉ domino ∧ (∀ w ∈ domino, z₀ 0 ≤ w 0) :=
  lmo_lexMinCell domino domino_finite ⟨_, Set.mem_insert _ _⟩

example : lmo_OrbitReachesLeftmost unitCell ucBase 0 := lmo_unitCell_reachesLeftmost

example : wei_WindingWitness unitCell ucBase :=
  lmo_windingWitness_of_reachesLeftmost unitCell ucBase 0 lmo_unitCell_minColumn
    unitCell_loop_isCycle lmo_unitCell_reachesLeftmost

example : lmo_lexKey ![2, 3] = toLex (2, 3) := rfl

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.LexMinOrientation
