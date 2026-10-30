/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHullUmlaufsatz

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHullUmlaufsatz`

* `shu_starHull_mpl_isCycle` (unconditional) for every boundary orbit of the star hull of the unit
  cell.
* `shu_windingWitness_of_minVertStepLeft` instantiated with a finite set (its residual hypothesis
  is the named predicate `shw_MinVertStepLeft`, satisfiable by the unit cell; see the StarHullWinding
  tests).
* Not tested: `shu_turningIsFullRevolution_of_saturating` (vacuous, its hypothesis is refuted) and
  `shu_turningIsFullRevolution_of_eulerCharOne` (circular, see the Stage B report).
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.StarHullUmlaufsatz

example (a : {e : Dart // IsBoundaryDart (ndt_StarHull unitCell) e}) :
    (mpl_orbitLoop (ndt_StarHull unitCell) a).IsCycle :=
  shu_starHull_mpl_isCycle unitCell unitCell_finite a

example (a : {e : Dart // IsBoundaryDart (ndt_StarHull unitCell) e})
    (h : shw_MinVertStepLeft (ndt_StarHull unitCell) a) :
    wei_WindingWitness (ndt_StarHull unitCell) a :=
  shu_windingWitness_of_minVertStepLeft unitCell unitCell_finite a h

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.StarHullUmlaufsatz
