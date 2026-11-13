/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































































import Mathlib
import Code.Walls.jc2_core
import Code.Walls.jc2_runframe
import Code.Walls.jc2_thinthickdichotomy
import Code.Walls.jc2_thinconn
import Code.Walls.jc2_thickshelf
import Code.Walls.jc3_earfootprint
import Code.Walls.jc3_clipsymmdiff
import Code.Walls.jc3_shelfcell
import Code.Walls.jc3_tailturneq
import Code.Lattice.BalancePreservingContraction

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice

































def jc3_OrbitSpliceDatum (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) : Prop :=
  ∃ (_ : (K \ {r}).Nonempty) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e}) (m m' n : ℕ),
    dartOrbitPeriod K a = m + n ∧
    dartOrbitPeriod (K \ {r}) a' = m' + n ∧
    (∀ i, i < n →
      (dartNext (K \ {r}))^[m' + i] a'.1 = (dartNext K)^[m + i] a.1 ∧
      bpc_NotProbed r ((dartNext K)^[m + i] a.1)) ∧
    jc_windowTurn (K \ {r}) a'.1 0 m' = jc_windowTurn K a.1 0 m






















theorem jc3_pendantClipMatch_of_splice (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (h : jc3_OrbitSpliceDatum K a r) :
    jc2_PendantClipMatch K a r := by
  obtain ⟨hne', a', m, m', n, hp, hp', htail, hbal⟩ := h
  refine ⟨hne', a', m, m', n, hp, hp', ?_, hbal⟩
  intro i hi
  obtain ⟨heq, hnp⟩ := htail i hi
  
  rw [heq]
  
  exact (bpc_turnZ_diff_singleton K r ((dartNext K)^[m + i] a.1) hnp).symm

















def jc3_SaturatingOrbitSplice : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
    ∀ (a : {e : Dart // IsBoundaryDart K e}),
      K ⊆ bpc_orbitFootprint K a →
      ∀ c len, jc2_RunFrame K c len → jc3_OrbitSpliceDatum K a (c + ![len, 0])








theorem jc3_saturatingEarMatch_of_splice (h : jc3_SaturatingOrbitSplice) :
    jc2_SaturatingEarMatch := by
  intro K hK hge a hsat c len hframe
  exact jc3_pendantClipMatch_of_splice K a (c + ![len, 0]) (h K hK hge a hsat c len hframe)























theorem jc3_splice_thin_or_thick (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hframe : jc2_RunFrame K c len) (hlen : 1 ≤ len) :
    (jc2_rightEnd c len + ![0, -1] ∉ K ∧ jc_IsPendantCell K (jc2_rightEnd c len)) ∨
      (jc2_rightEnd c len + ![0, -1] ∈ K ∧ ¬ jc_IsPendantCell K (jc2_rightEnd c len)) :=
  (jc2_thinThickDichotomy K c len hframe.isRun).dichotomy hlen







theorem jc3_thin_reroute_cellConnected (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hconn : CellConnected K) (hframe : jc2_RunFrame K c len) (hlen : 1 ≤ len)
    (hthin : (c + ![len, 0] : Site 2) + ![0, -1] ∉ K) :
    CellConnected (K \ {(c + ![len, 0] : Site 2)}) :=
  jc2_thinFingerClip_cellConnected K c len hconn hframe.isRun hlen hthin









theorem jc3_thick_reroute_target (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hthick : jc2_FullyThick K c len) (hlen : 0 ≤ len) :
    jc3_downCell c len ∈ K \ {jc3_runRightEnd c len} ∧
      (hypercubicLattice 2).Adj (jc3_runRightEnd c len) (jc3_downCell c len) :=
  jc3_rerouteTarget_in_clip K c len hthick hlen













theorem jc3_balanceSaturatingContraction_of_splice (h : jc3_SaturatingOrbitSplice) :
    bpc_BalanceSaturatingContraction :=
  jc2_balanceSaturatingContraction_of_earMatch (jc3_saturatingEarMatch_of_splice h)





theorem jc3_balancePreservingContraction_of_splice (h : jc3_SaturatingOrbitSplice) :
    BalancePreservingContraction :=
  jc2_balancePreservingContraction_of_earMatch (jc3_saturatingEarMatch_of_splice h)






theorem jc3_starHull_totalTurn_eq_four_of_splice (h : jc3_SaturatingOrbitSplice)
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 :=
  jc2_starHull_totalTurn_eq_four_of_earMatch (jc3_saturatingEarMatch_of_splice h) K hSK hne a















theorem jc3_pendantClipMatch_of_splice' (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) :
    jc3_OrbitSpliceDatum K a r → jc2_PendantClipMatch K a r :=
  jc3_pendantClipMatch_of_splice K a r















theorem jc3_domino_core_witness :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < domino.ncard ∧ cornerBalance K' a' = cornerBalance domino dmBase :=
  jc2_domino_core_witness





theorem jc3_domino_thin_ear : jc_IsPendantCell domino ((![0, 0] : Site 2) + ![1, 0]) :=
  jc2_domino_thin_book_ear





theorem jc3_domino_thin_clip_cellConnected :
    CellConnected (domino \ {(![0, 0] : Site 2) + ![1, 0]}) :=
  jc2_domino_thinConn












































end Walls

end StatMech
