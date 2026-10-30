/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHullPeriod
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHullWinding
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.GaussBonnet
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CornerBalanceOrbit

/-!
# Umlaufsatz statements for boundary orbits of star hulls

The star hull of a finite set has no diagonal touches, so the face loop of each of its boundary
orbits is a simple cycle in the square lattice. The discrete Umlaufsatz then says that each such
orbit turns by exactly one full revolution: its total signed turning is `4` or `-4` quarter turns
(`TurningIsFullRevolution`). This file collects the forms of that statement available for star
hulls; none of them is an unconditional proof.

* `shu_turningIsFullRevolution_of_saturating` assumes `bpc_BalanceSaturatingContraction`, which is
  false (`not_bpc_BalanceSaturatingContraction`), so it is vacuous.
* `shu_turningIsFullRevolution_of_eulerCharOne` assumes `EulerCharOne`, which for orbits of length
  at least three is equivalent to the conclusion (`shu_eulerCharOne_iff_balanceIsFour` together
  with `simplePolygonCornerBalance_iff`), so it is a restatement.

An unconditional discrete Umlaufsatz for simple closed lattice walks, stated for direction
sequences, is `StatMech.Onsager.GeneralUmlaufsatz.turnSum_eq_four_or_neg_four`; it is not connected
to boundary orbits here.

The file also records the cycle property of star hull face loops and the resulting winding
witness from a leftmost leftward vertical step.

## Main results

* `StatMech.Lattice.shu_turningIsFullRevolution_of_saturating`: Umlaufsatz for star hull orbits
  under the (false) saturated contraction hypothesis.
* `StatMech.Lattice.shu_turningIsFullRevolution_of_eulerCharOne`: Umlaufsatz for star hull orbits
  under the equivalent hypothesis `EulerCharOne`.
* `StatMech.Lattice.shu_starHull_mpl_isCycle`: face loops of boundary orbits of star hulls of
  finite sets are cycles.
* `StatMech.Lattice.shu_windingWitness_of_minVertStepLeft`: such an orbit has a winding witness
  when its leftmost vertical step comes from a leftward dart.

## References

* H. Hopf, *Über die Drehung der Tangenten und Sehnen ebener Kurven*, Compositio Math. 2 (1935)
  50-62
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- The face loop of every boundary orbit of the star hull of a finite set is a cycle. -/
theorem shu_starHull_mpl_isCycle (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    (mpl_orbitLoop (ndt_StarHull K) a).IsCycle :=
  shw_starHull_mpl_isCycle K a (shp_starHull_period_ge_three K hK a)

/-- Hopf's Umlaufsatz for boundary orbits of star hulls, conditional form: under
`bpc_BalanceSaturatingContraction`, every boundary orbit of the star hull of a finite nonempty set
turns by `±4` quarter turns.

The literature statement (H. Hopf, 1935, discrete form) holds for every orbit whose face loop is a
simple cycle, hence for all boundary orbits of star hulls of finite sets, including orbits around
holes. Here, however, the hypothesis `bpc_BalanceSaturatingContraction` is false
(`not_bpc_BalanceSaturatingContraction`), so this theorem is vacuous. -/
theorem shu_turningIsFullRevolution_of_saturating (K : Set (Site 2)) (hK : K.Finite)
    (hne : K.Nonempty) (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hsat : bpc_BalanceSaturatingContraction) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  bpc_totalTurn_eq_four_of_saturating K (starHull_finite K hK) (hne.mono (ndt_subset_starHull K))
    a hsat

/-- Hopf's Umlaufsatz for boundary orbits of star hulls, `EulerCharOne` form: if the boundary orbit
of the star hull of a finite set has Euler characteristic one in the sense of `EulerCharOne`
(revolution count `±1`), it turns by `±4` quarter turns.

For orbits of length at least three, which is automatic here, `EulerCharOne` is equivalent to the
conclusion (`shu_eulerCharOne_iff_balanceIsFour`, `simplePolygonCornerBalance_iff`), so this is a
restatement rather than a proof of the Umlaufsatz. See also
`turningIsFullRevolution_of_eulerCharOne` for arbitrary sets. -/
theorem shu_turningIsFullRevolution_of_eulerCharOne (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (h : EulerCharOne (ndt_StarHull K) a) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  turningIsFullRevolution_of_eulerCharOne _ a (shp_starHull_period_ge_three K hK a) h

/-- For boundary orbits of star hulls of finite sets, `EulerCharOne` is equivalent to corner
balance `±4`. -/
theorem shu_eulerCharOne_iff_balanceIsFour (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    EulerCharOne (ndt_StarHull K) a ↔ BalanceIsFour (ndt_StarHull K) a :=
  eulerCharOne_iff_balanceIsFour (ndt_StarHull K) a (shp_starHull_period_ge_three K hK a)

/-- A boundary orbit of the star hull of a finite set has a winding witness when a leftmost
vertical step of its face loop comes from a leftward dart. -/
theorem shu_windingWitness_of_minVertStepLeft (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hres : shw_MinVertStepLeft (ndt_StarHull K) a) :
    wei_WindingWitness (ndt_StarHull K) a :=
  shw_windingWitness_of_minLeft (ndt_StarHull K) a (shu_starHull_mpl_isCycle K hK a) hres

end Lattice

end StatMech
