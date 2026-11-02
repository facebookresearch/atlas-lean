/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.WindingWitnessOfExterior

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.WindingWitnessOfExterior`

* No test of the conditional lemmas: their exterior hypothesis `hExt` fails for the unit cell
  and the domino (Stage B: `exc_oldExteriorConnected_false`, `g4_wwc_globalExt_false`) and is
  expected to fail for every set. Recorded as an unsatisfiable hypothesis in the report.
* The unit-cell winding witness (the conclusion) is checked from the unconditional route.
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.WindingWitnessOfExterior

example : wei_WindingWitness unitCell ucBase := wei_unitCell_windingWitness

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.WindingWitnessOfExterior
