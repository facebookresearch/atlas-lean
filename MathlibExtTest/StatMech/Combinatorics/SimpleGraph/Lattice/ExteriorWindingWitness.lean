/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ExteriorWindingWitness

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.ExteriorWindingWitness`

* Not covered: all three results need `exc_OffSupportReachesExterior K a`, for which no concrete
  instance is available (see the ExteriorConnected tests). The other hypothesis,
  `exc_SupportOddInK`, holds for the unit cell.
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.ExteriorWindingWitness

example : exc_SupportOddInK unitCell ucBase := exc_unitCell_supportOddInK

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.ExteriorWindingWitness
