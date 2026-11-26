/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSegmentDownCounterexample

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.KingSegmentDownCounterexample`

* The staircase walk `ksd_stair`: its off-support interior is `{(1, 1), (2, 2)}`, it is 4-thin and
  king row-linked at `(1, 1)`, yet violates the king segment-down condition
  (`ksd_residue_false_but_theorem_true`).
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSegmentDownCounterexample

example : jil_offSupportInterior ksd_stair = {(![1, 1] : Site 2), (![2, 2] : Site 2)} :=
  ksd_interior_eq

example : mci_FourThin ksd_stair ∧ mci_KingRowLinked ksd_stair (![1, 1] : Site 2) ∧
    ¬ kif_KingSegmentDown ksd_stair (![1, 1] : Site 2) :=
  ksd_residue_false_but_theorem_true

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.KingSegmentDownCounterexample
