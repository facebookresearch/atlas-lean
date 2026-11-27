/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ExitOrbitAnchoredCycle

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.ExitOrbitAnchoredCycle`

* Unit-cell instance of the winding condition behind `acc_ExitDartWinds`: the face loop of the
  unit cell (the exit orbit of the all-closed configuration) is a cycle and the origin has odd ray
  count; the loop visits a face left of the origin.
* Not covered: `acc_pc_lt_one_of_exitDartWinds` needs `acc_ExitDartWinds` for every configuration
  with a finite origin cluster (unproved geometric input, see the Stage B report).
-/

@[expose] public section

open StatMech.Lattice
open StatMech.Percolation (origin)

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.ExitOrbitAnchoredCycle

example : (mpl_orbitFaceLoop unitCell ucBase).IsCycle ∧
    ¬ Even (jec_rayCount (origin 2) (mpl_orbitLoop unitCell ucBase)) :=
  acc_unitCell_winds

example : ∃ f ∈ (mpl_orbitLoop unitCell ucBase).support, f 0 ≤ -1 :=
  acc_unitCell_hasLeftSupportFace

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.ExitOrbitAnchoredCycle
