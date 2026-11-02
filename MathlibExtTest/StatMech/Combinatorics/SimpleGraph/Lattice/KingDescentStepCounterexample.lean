/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingDescentStepCounterexample

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingDescentStepCounterexample`

* The walk `kda_stairDR`: its off-support interior has three sites, it is 4-thin and king
  row-linked at `(3, 1)`, yet violates one-step king descent
  (`kda_descentStep_false_but_theorem_true`).
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingDescentStepCounterexample

example : jil_offSupportInterior kda_stairDR =
    {(![1, 2] : Site 2), (![2, 2] : Site 2), (![3, 1] : Site 2)} :=
  kda_interior_eq

example : mci_FourThin kda_stairDR ∧ mci_KingRowLinked kda_stairDR (![3, 1] : Site 2) ∧
    ¬ kda_KingDescentStep kda_stairDR (![3, 1] : Site 2) :=
  kda_descentStep_false_but_theorem_true

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingDescentStepCounterexample
