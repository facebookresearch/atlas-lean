/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TotalTurnFour
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.TotalTurnFour`

* `ttf_totalTurn_eq_four_of_winds` and `ttf_winds_iff` for every boundary orbit of the star hull
  of a set, as an equivalence instance; `ttf_eulerCharOne_iff_winds` under period `≥ 3`.
* The conditional `ttf_totalTurn_eq_four_of_balancePreservingContraction` was removed: its
  hypothesis is refuted by `not_balancePreservingContraction`.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TotalTurnFour

example (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (h4 : totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4) :
    ttf_WindsAtMostOnce K a ∧ ttf_WindsAtLeastOnce K a :=
  (ttf_winds_iff K a).mpr (Or.inr h4)

example (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a)
    (h4 : totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4) :
    EulerCharOne (ndt_StarHull K) a :=
  (ttf_eulerCharOne_iff_winds K a hp).mpr ((ttf_winds_iff K a).mpr (Or.inr h4))

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TotalTurnFour
