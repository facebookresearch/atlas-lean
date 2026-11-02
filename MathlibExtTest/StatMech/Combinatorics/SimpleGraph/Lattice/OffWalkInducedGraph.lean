/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OffWalkInducedGraph
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.OffWalkInducedGraph`

* `icc_card_two_dichotomy` on `Bool`.
* `icc_induce_reachable_iff` for the trivial closed walk at the origin: reachability in
  `icc_offComplGraph` is reachability in `offSupport`.
-/

@[expose] public section

open StatMech.Lattice SimpleGraph

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OffWalkInducedGraph

example (c : Bool) : c = true ∨ c = false :=
  icc_card_two_dichotomy (by simp) (by decide) c

/-- The one-vertex closed walk at the origin. -/
abbrev W0 : (hypercubicLattice 2).Walk ![0, 0] ![0, 0] := Walk.nil

example (x y : {z : Site 2 // z ∉ W0.support}) :
    (icc_offComplGraph W0).Reachable x y ↔ (offSupport W0).Reachable (x : Site 2) y :=
  icc_induce_reachable_iff _

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OffWalkInducedGraph
