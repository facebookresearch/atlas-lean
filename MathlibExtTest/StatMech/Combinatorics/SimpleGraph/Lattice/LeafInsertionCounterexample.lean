/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.LeafInsertionCounterexample
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.LeafInsertionCounterexample`

* The counterexample: the open ring `lrc_ringS` has connected complement (`lrc_ring_connected`),
  closing it with `lrc_uPrime = (1, 0)` disconnects the origin (`lrc_insert_not_connected`), so
  `arcns_LeafRemovable lrc_ringS lrc_uPrime` fails (`lrc_leafRemovable_false`) and the
  leaf-insertion hypothesis for all arcs is false (`lrc_arc_leafHypothesis_false`).
* `lrc_uPrime` evaluated; the origin is not in `lrc_ringS`.
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.LeafInsertionCounterexample

example : lrc_uPrime 0 = 1 ∧ lrc_uPrime 1 = 0 := by simp [lrc_uPrime]

example : arcns_OffSupportConnected lrc_ringS := lrc_ring_connected

example : ¬ arcns_OffSupportConnected (insert lrc_uPrime lrc_ringS) := lrc_insert_not_connected

example : ¬ arcns_LeafRemovable lrc_ringS lrc_uPrime := lrc_leafRemovable_false

example : ¬ (∀ (a b c : Site 2) (h : (hypercubicLattice 2).Adj a b)
    (q : (hypercubicLattice 2).Walk b c), (Walk.cons h q).IsPath →
      arcns_LeafRemovable {z : Site 2 | z ∈ q.support} a) :=
  lrc_arc_leafHypothesis_false

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.LeafInsertionCounterexample
