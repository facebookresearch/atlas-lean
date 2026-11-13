/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.TurningNumber
import Code.Lattice.CornerBalance
import Code.Lattice.EarRemoval
import Code.Lattice.EarExistence
import Code.Lattice.EarContraction
import Code.Lattice.GaussBonnet
import Code.Lattice.GaussBonnetEar
import Code.Lattice.BalanceContraction
import Code.Lattice.BalancePreservingContraction
import Code.Lattice.TotalTurnFour
import Code.Lattice.NoDiagTouchClose
import Code.Lattice.StarHullFinite
import Code.Lattice.StarHullPeriod
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.WindingEarInduction
import Code.Lattice.StarHullWinding

open Set SimpleGraph Function

namespace StatMech

namespace Lattice










theorem shu_starHull_finite (K : Set (Site 2)) (hK : K.Finite) : (ndt_StarHull K).Finite :=
  starHull_finite K hK



theorem shu_starHull_nonempty (K : Set (Site 2)) (hne : K.Nonempty) : (ndt_StarHull K).Nonempty :=
  hne.mono (ndt_subset_starHull K)





theorem shu_starHull_period_ge_three (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    3 ≤ dartOrbitPeriod (ndt_StarHull K) a :=
  shp_starHull_period_ge_three K hK a






theorem shu_starHull_mpl_isCycle (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    (mpl_orbitLoop (ndt_StarHull K) a).IsCycle :=
  shw_starHull_mpl_isCycle K a (shu_starHull_period_ge_three K hK a)

















theorem shu_turningIsFullRevolution_of_saturating (K : Set (Site 2)) (hK : K.Finite)
    (hne : K.Nonempty) (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hsat : bpc_BalanceSaturatingContraction) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  bpc_totalTurn_eq_four_of_saturating K (shu_starHull_finite K hK) (shu_starHull_nonempty K hne) a
    hsat




theorem shu_totalTurn_eq_four_of_saturating (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hsat : bpc_BalanceSaturatingContraction) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 :=
  shu_turningIsFullRevolution_of_saturating K hK hne a hsat












theorem shu_turningIsFullRevolution_of_eulerCharOne (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (h : EulerCharOne (ndt_StarHull K) a) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  ttf_totalTurn_eq_four_of_eulerCharOne K a (shu_starHull_period_ge_three K hK a) h




theorem shu_totalTurn_eq_four_of_eulerCharOne (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (h : EulerCharOne (ndt_StarHull K) a) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 :=
  shu_turningIsFullRevolution_of_eulerCharOne K hK a h










theorem shu_totalTurn_eq_four_of_balanceIsFour (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (h : BalanceIsFour (ndt_StarHull K) a) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 := by
  unfold BalanceIsFour at h
  rwa [cornerBalance_eq_totalTurnZ] at h










theorem shu_cornerBalance_eq_four_revCount (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    cornerBalance (ndt_StarHull K) a = 4 * revCount (ndt_StarHull K) a :=
  cornerBalance_eq_four_revCount (ndt_StarHull K) a





theorem shu_eulerCharOne_iff_balanceIsFour (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    EulerCharOne (ndt_StarHull K) a ↔ BalanceIsFour (ndt_StarHull K) a :=
  eulerCharOne_iff_balanceIsFour (ndt_StarHull K) a (shu_starHull_period_ge_three K hK a)




theorem shu_balanceIsFour_iff_revCount_pm_one (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    BalanceIsFour (ndt_StarHull K) a ↔
      (revCount (ndt_StarHull K) a = 1 ∨ revCount (ndt_StarHull K) a = -1) :=
  balanceIsFour_iff_revCount_pm_one (ndt_StarHull K) a



















theorem shu_windingWitness_of_minVertStepLeft (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hres : shw_MinVertStepLeft (ndt_StarHull K) a) :
    wei_WindingWitness (ndt_StarHull K) a :=
  shw_windingWitness_of_minLeft (ndt_StarHull K) a (shu_starHull_mpl_isCycle K hK a) hres











theorem shu_unitCell_totalTurn_eq_four :
    totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 4 ∨
      totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 :=
  unitCell_turningIsFullRevolution




theorem shu_domino_totalTurn_eq_four :
    totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = 4 ∨
      totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = -4 :=
  domino_turningIsFullRevolution




theorem shu_unitCell_minVertStepLeft : shw_MinVertStepLeft unitCell ucBase :=
  shw_unitCell_minVertStepLeft




theorem shu_unitCell_windingWitness : wei_WindingWitness unitCell ucBase :=
  wei_unitCell_windingWitness



theorem shu_unitCell_balanceIsFour : BalanceIsFour unitCell ucBase :=
  unitCell_balanceIsFour












































end Lattice

end StatMech
