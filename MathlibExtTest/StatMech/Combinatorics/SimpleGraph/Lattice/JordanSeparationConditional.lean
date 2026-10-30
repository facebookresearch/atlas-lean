/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanSeparationConditional
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanSeparationConditional`

* `jsc_JordanSeparates_inside_satisfiable`: the first clause of `jsc_JordanSeparates` holds for
  the unit square loop.
* `jsc_exists_outside` for the unit square loop.
* The conditional headlines (`jsc_separation_of_JordanSeparates`, `jsc_cycle_separation`) are not
  instantiated: the full `jsc_JordanSeparates` (connectivity of both sides) is not proved for any
  loop in the library.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.JordanSeparationConditional

example : ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a), ∃ p, ¬ Even (jec_rayCount p Vc) :=
  jsc_JordanSeparates_inside_satisfiable

example : ∃ q : Site 2, q ∉ jec_leftRegion jsc_unitSquareLoop ∧
    ∀ p ∈ jsc_unitSquareLoop.support, p 0 ≤ q 0 - 1 :=
  jsc_exists_outside jsc_unitSquareLoop

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.JordanSeparationConditional
