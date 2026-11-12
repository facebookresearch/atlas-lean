/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































import Mathlib
import Code.Walls.jc2_engine
import Code.Walls.jc2_runframe
import Code.Walls.jc2_thinpendant
import Code.Walls.jc2_thinconn
import Code.Walls.jc2_thinthickdichotomy
import Code.Walls.jc2_thickshelf
import Code.Walls.jc_core
import Code.Lattice.BalancePreservingContraction

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice





















def jc2_OrbitMatchAt (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
    (a' : {e : Dart // IsBoundaryDart K' e}) (m m' n : ℕ),
    K'.ncard < K.ncard ∧
    dartOrbitPeriod K a = m + n ∧
    dartOrbitPeriod K' a' = m' + n ∧
    (∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] a.1) = turnZ K' ((dartNext K')^[m' + i] a'.1)) ∧
    jc_windowTurn K' a'.1 0 m' = jc_windowTurn K a.1 0 m










theorem jc2_contraction_of_orbitMatch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : jc2_OrbitMatchAt K a) :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a := by
  obtain ⟨K', hK'fin, hK'ne, a', m, m', n, hcard, hp, hp', hmatch, hbal⟩ := h
  refine ⟨K', hK'fin, hK'ne, a', hcard, ?_⟩
  rw [cornerBalance_eq_totalTurnZ, cornerBalance_eq_totalTurnZ, hp, hp']
  exact jc2_engine K K' a.1 a'.1 m m' n hmatch hbal
















theorem jc2_orbitMatch_of_contraction (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (h : ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a) :
    jc2_OrbitMatchAt K a := by
  obtain ⟨K', hK'fin, hK'ne, a', hcard, hbalance⟩ := h
  refine ⟨K', hK'fin, hK'ne, a', dartOrbitPeriod K a, dartOrbitPeriod K' a', 0,
    hcard, by omega, by omega, by intro i hi; omega, ?_⟩
  rw [jc_windowTurn_eq, jc_windowTurn_eq, ← umEar_totalTurnZ_eq_window,
      ← umEar_totalTurnZ_eq_window, ← cornerBalance_eq_totalTurnZ, ← cornerBalance_eq_totalTurnZ]
  exact hbalance








theorem jc2_orbitMatch_iff_contraction (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    jc2_OrbitMatchAt K a ↔
      ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
        (a' : {e : Dart // IsBoundaryDart K' e}),
        K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a :=
  ⟨jc2_contraction_of_orbitMatch K a, jc2_orbitMatch_of_contraction K a⟩
















def jc2_PendantClipMatch (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) : Prop :=
  ∃ (_ : (K \ {r}).Nonempty) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e}) (m m' n : ℕ),
    dartOrbitPeriod K a = m + n ∧
    dartOrbitPeriod (K \ {r}) a' = m' + n ∧
    (∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] a.1) =
        turnZ (K \ {r}) ((dartNext (K \ {r}))^[m' + i] a'.1)) ∧
    jc_windowTurn (K \ {r}) a'.1 0 m' = jc_windowTurn K a.1 0 m



theorem jc2_pendantClip_card_lt (K : Set (Site 2)) (hK : K.Finite) (r : Site 2)
    (hr : r ∈ K) : (K \ {r}).ncard < K.ncard := by
  have hsub : (K \ {r}) ⊂ K := by
    rw [Set.ssubset_iff_of_subset Set.diff_subset]
    exact ⟨r, hr, by simp⟩
  exact Set.ncard_lt_ncard hsub hK







theorem jc2_contraction_of_pendantClipMatch (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) (hr : r ∈ K)
    (h : jc2_PendantClipMatch K a r) :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a := by
  obtain ⟨hne', a', m, m', n, hp, hp', hmatch, hbal⟩ := h
  refine ⟨K \ {r}, hK.subset Set.diff_subset, hne', a',
    jc2_pendantClip_card_lt K hK r hr, ?_⟩
  rw [cornerBalance_eq_totalTurnZ, cornerBalance_eq_totalTurnZ, hp, hp']
  exact jc2_engine K (K \ {r}) a.1 a'.1 m m' n hmatch hbal


























def jc2_SaturatingEarMatch : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
    ∀ (a : {e : Dart // IsBoundaryDart K e}),
      K ⊆ bpc_orbitFootprint K a →
      ∀ c len, jc2_RunFrame K c len → jc2_PendantClipMatch K a (c + ![len, 0])









theorem jc2_balanceSaturatingContraction_of_earMatch
    (h : jc2_SaturatingEarMatch) : bpc_BalanceSaturatingContraction := by
  intro K hK hge a hsat
  
  have hne : K.Nonempty := by
    rw [← Set.ncard_pos hK]; omega
  obtain ⟨c, len, hframe⟩ := jc2_runFrame K hK hne
  
  set r : Site 2 := c + ![len, 0] with hr
  have hrK : r ∈ K := hframe.isRun.run_mem len hframe.isRun.len_nonneg (le_refl len)
  
  have hmatch : jc2_PendantClipMatch K a r := h K hK hge a hsat c len hframe
  exact jc2_contraction_of_pendantClipMatch K hK a r hrK hmatch













theorem jc2_balancePreservingContraction_of_earMatch
    (h : jc2_SaturatingEarMatch) : BalancePreservingContraction :=
  bpc_balancePreservingContraction_of_saturating
    (jc2_balanceSaturatingContraction_of_earMatch h)






theorem jc2_turningIsFullRevolution_of_earMatch (h : jc2_SaturatingEarMatch)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) : TurningIsFullRevolution K a :=
  turningIsFullRevolution_of_contraction (jc2_balancePreservingContraction_of_earMatch h)
    K hK hne a






theorem jc2_starHull_turningIsFullRevolution_of_earMatch (h : jc2_SaturatingEarMatch)
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  gbe_totalTurn_eq_four_of_contraction K hSK hne a
    (jc2_balancePreservingContraction_of_earMatch h)






theorem jc2_starHull_totalTurn_eq_four_of_earMatch (h : jc2_SaturatingEarMatch)
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 :=
  jc2_starHull_turningIsFullRevolution_of_earMatch h K hSK hne a














theorem jc2_saturating_has_runFrame (K : Set (Site 2)) (hK : K.Finite) (hge : 2 ≤ K.ncard) :
    ∃ c len, jc2_RunFrame K c len := by
  have hne : K.Nonempty := by rw [← Set.ncard_pos hK]; omega
  exact jc2_runFrame K hK hne










theorem jc2_runFrame_thinThickDichotomy (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hframe : jc2_RunFrame K c len) : jc2_ThinThickDichotomy K c len :=
  jc2_thinThickDichotomy K c len hframe.isRun









theorem jc2_thin_book_ear_cellConnected (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hconn : CellConnected K) (hframe : jc2_RunFrame K c len) (hlen : 1 ≤ len)
    (hthin : (c + ![len, 0] : Site 2) + ![0, -1] ∉ K) :
    CellConnected (K \ {(c + ![len, 0] : Site 2)}) :=
  jc2_thinFingerClip_cellConnected K c len hconn hframe.isRun hlen hthin









theorem jc2_unitCell_core_balanceIsFour : BalanceIsFour unitCell ucBase :=
  jc_unitCell_core_balanceIsFour









theorem jc2_domino_core_witness :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < domino.ncard ∧ cornerBalance K' a' = cornerBalance domino dmBase :=
  jc_domino_core_witness






theorem jc2_domino_book_ear : jc2_RunFrame domino (![0, 0] : Site 2) 1 :=
  jc2_domino_runFrame






theorem jc2_domino_thin_book_ear : jc_IsPendantCell domino ((![0, 0] : Site 2) + ![1, 0]) :=
  jc_domino_rightEnd_pendant











































end Walls

end StatMech
