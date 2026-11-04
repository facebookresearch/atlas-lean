/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.LeftFenceAnchor

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.LeftFenceAnchor`

* `lfa_starHull_exists_windingWitness` (unconditional) at the unit cell and the domino.
* `lfa_leftFence_anchor` at the unit cell; the left fence dart of the unit cell is a boundary dart
  whose orbit reaches the leftmost column.
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.LeftFenceAnchor

example : ∃ a : {e : Dart // IsBoundaryDart (ndt_StarHull unitCell) e},
    wei_WindingWitness (ndt_StarHull unitCell) a :=
  lfa_starHull_exists_windingWitness unitCell unitCell_finite (Set.singleton_nonempty _)

example : ∃ a : {e : Dart // IsBoundaryDart (ndt_StarHull domino) e},
    wei_WindingWitness (ndt_StarHull domino) a :=
  lfa_starHull_exists_windingWitness domino domino_finite ⟨_, Set.mem_insert _ _⟩

example : ∃ z₀ ∈ unitCell, IsBoundaryDart unitCell (leftDart z₀) ∧ (∀ w ∈ unitCell, z₀ 0 ≤ w 0) :=
  lfa_leftFence_anchor unitCell unitCell_finite (Set.singleton_nonempty _)

example : lmo_OrbitReachesLeftmost unitCell
    ⟨leftDart (![0, 0] : Site 2), lfa_unitCell_leftFence_isBoundaryDart⟩ 0 :=
  lfa_unitCell_leftFence_reachesLeftmost

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.LeftFenceAnchor
