/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.WindingWitness
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.WindingWitness`

* `wwit_unitSquareLoop_inside_odd`: `(1, 1)` has odd ray count for the unit square loop.
* `wwit_localTurn_mem` as an instance.
* `wwit_winding_witness_of_tailOdd` and `wwit_starHull_bdEdgeMatch_of_tailOdd` are not
  instantiated: `wwit_TailOdd` needs an explicit computation of an orbit loop (see the Stage B
  report).
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.WindingWitness

example : ¬ Even (jec_rayCount (![1, 1] : Site 2) wwit_unitSquareLoop) :=
  wwit_unitSquareLoop_inside_odd

example (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hmult : usc_FaceMultiplicityOne K a) (f : Site 2) :
    usc_localTurn K a f = 1 ∨ usc_localTurn K a f = 0 ∨ usc_localTurn K a f = -1 :=
  wwit_localTurn_mem K a hmult f

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.WindingWitness
