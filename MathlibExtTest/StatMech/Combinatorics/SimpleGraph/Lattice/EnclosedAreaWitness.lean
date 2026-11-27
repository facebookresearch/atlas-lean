/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.EnclosedAreaWitness

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.EnclosedAreaWitness`

* `eaw_InteriorSubset` holds for the unit cell, and so do all three conjuncts of
  `eaw_LoopWindsRegion` for its boundary orbit.
* `eaw_windingWitness_of_cycle_interior` is instantiated at the unit cell (its hypotheses are
  satisfiable).
* `eaw_cycle_oddCell` is applied to the face loop of the unit cell, which is a cycle.
* The refutation `not_eaw_LoopWindsRegion` is restated.
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.EnclosedAreaWitness

example : eaw_InteriorSubset unitCell ucBase := eaw_unitCell_interiorSubset

example : wei_WindingWitness unitCell ucBase :=
  eaw_windingWitness_of_cycle_interior unitCell ucBase eaw_unitCell_loopWindsRegion.1
    eaw_unitCell_loopWindsRegion.2.1 eaw_unitCell_loopWindsRegion.2.2

example : ∃ z : Site 2, jec_rayCount z (mpl_orbitLoop unitCell ucBase) = 1 :=
  eaw_cycle_oddCell _ (mpl_orbitLoop_isCycle unitCell ucBase eaw_unitCell_loopWindsRegion.1
    (orbitFace_injOn_of_noPinch _ _ eaw_unitCell_loopWindsRegion.2.1))

example : ¬ eaw_LoopWindsRegion := not_eaw_LoopWindsRegion

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.EnclosedAreaWitness
