/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.EarContraction
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.EarContraction`

* `singleton_cornerBalance` and `unitCell_cornerBalance`: corner balance `-4`.
* `cornerBalance_eq_totalTurnZ` on a one-site set: total turning `-4`.
* `cutWitness_diff_not_cellConnected` (removing an extreme cell can disconnect a cell set) and
  `CellConnected` of the four-cell witness itself is not asserted; the counterexample is restated.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.EarContraction

example (a : {e : Dart // IsBoundaryDart ({0} : Set (Site 2)) e}) :
    totalTurnZ ({0} : Set (Site 2)) a.1 (dartOrbitPeriod ({0} : Set (Site 2)) a) = -4 := by
  rw [← cornerBalance_eq_totalTurnZ]; exact singleton_cornerBalance 0 a

example : cornerBalance unitCell ucBase = -4 := unitCell_cornerBalance ucBase (Or.inl rfl)

example : ¬ CellConnected (cutWitness \ {![1, 1]}) := cutWitness_diff_not_cellConnected

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.EarContraction
