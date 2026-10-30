/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.WindingEarInduction

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.WindingEarInduction`

* `wei_WindingWitness` holds for every boundary orbit of a single site and for the unit cell.
* The hole orbit of the four-site ring `bpc_holeRing` has period `4`, and the refutation
  `not_wei_WindingSaturatingWitness` is restated.
* Ray counts of face loops are translation invariant (`wei_rayCount_trans`), instantiated at the
  unit cell.
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.WindingEarInduction

example (v : Site 2) (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}) :
    wei_WindingWitness ({v} : Set (Site 2)) a :=
  wei_singleton_windingWitness v a

example : wei_WindingWitness unitCell ucBase := wei_unitCell_windingWitness

example : dartOrbitPeriod bpc_holeRing bpc_holeBase = 4 := wei_holeBase_period

example : ¬ wei_WindingSaturatingWitness := not_wei_WindingSaturatingWitness

example (w z : Site 2) :
    jec_rayCount (z + w) (mpl_orbitLoop (transSet w unitCell) (transSub unitCell w ucBase))
      = jec_rayCount z (mpl_orbitLoop unitCell ucBase) :=
  wei_rayCount_trans unitCell w ucBase z

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.WindingEarInduction
