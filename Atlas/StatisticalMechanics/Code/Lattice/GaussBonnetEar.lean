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
import Code.Lattice.UmlaufsatzEar
import Code.Lattice.Umlaufsatz
import Code.Lattice.UmlaufsatzSingleCycle
import Code.Lattice.NoDiagTouchClose
import Code.Lattice.WindingWitness

open SimpleGraph Function Set Finset

namespace StatMech

namespace Lattice











theorem gbe_faceLabel_injOn (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hmult : usc_FaceMultiplicityOne K a) :
    Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) := by
  rw [usc_faceInjOn_iff_visit_le_one K a]
  intro f
  rcases Nat.eq_zero_or_pos (usc_visitSet K a f).card with h0 | hpos
  · omega
  · rw [hmult f hpos]






theorem gbe_orbitFaces_card_eq_period (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hmult : usc_FaceMultiplicityOne K a) :
    (usc_orbitFaces K a).card = dartOrbitPeriod K a := by
  classical
  unfold usc_orbitFaces
  rw [Finset.card_image_of_injOn]
  · rw [Finset.card_range]
  · 
    intro i hi j hj hij
    rw [Finset.coe_range, Set.mem_Iio] at hi hj
    exact gbe_faceLabel_injOn K a hmult (Set.mem_Iio.mpr hi) (Set.mem_Iio.mpr hj) hij





theorem gbe_starHull_orbitFaces_card_eq_period (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    (usc_orbitFaces (ndt_StarHull K) a).card = dartOrbitPeriod (ndt_StarHull K) a :=
  gbe_orbitFaces_card_eq_period (ndt_StarHull K) a (ndt_faceMultiplicityOne K a)















theorem gbe_ear_first_turn (K : Set (Site 2)) (c : Site 2) (hc : IsExtremeCell K c) :
    turnZ K ((dartNext K)^[0] (leftDart c)) = -1 :=
  umEar_extremeCell_ear_first_turn K c hc





theorem gbe_exists_convex_ear (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ e : Dart, IsBoundaryDart K e ∧ turnZ K e = -1 :=
  exists_convex_corner_dart K hK hne














theorem gbe_ear_step_preserves_turn (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : umEar_windowTurn K' e' 0 m' = umEar_windowTurn K e 0 m) :
    totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) :=
  umEar_contraction_preserves_turning K K' e e' m m' n hmatch hbal






theorem gbe_ear_step_preserves_turn_balance (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : umEar_windowRight K' e' 0 m' - umEar_windowLeft K' e' 0 m' =
            umEar_windowRight K e 0 m - umEar_windowLeft K e 0 m) :
    totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) :=
  umEar_contraction_preserves_turning_balance K K' e e' m m' n hmatch hbal











theorem gbe_singleton_totalTurn_eq_four (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}) :
    totalTurnZ ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) = 4 ∨
      totalTurnZ ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) = -4 := by
  have h := singleton_balanceIsFour v a
  unfold BalanceIsFour at h
  rw [cornerBalance_eq_totalTurnZ] at h
  exact h






















theorem gbe_totalTurn_eq_four_of_contraction (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hcontr : BalancePreservingContraction) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  turningIsFullRevolution_of_contraction hcontr (ndt_StarHull K) hSK hne a






theorem gbe_totalTurn_eq_four_value_of_contraction (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hcontr : BalancePreservingContraction) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 :=
  gbe_totalTurn_eq_four_of_contraction K hSK hne a hcontr






theorem gbe_starHull_exists_convex_corner_of_contraction (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hcontr : BalancePreservingContraction) :
    (∃ f ∈ usc_orbitFaces (ndt_StarHull K) a, usc_localTurn (ndt_StarHull K) a f = 1) ∨
      (∃ f ∈ usc_orbitFaces (ndt_StarHull K) a, usc_localTurn (ndt_StarHull K) a f = -1) :=
  wwit_starHull_exists_convex_corner K a
    (gbe_totalTurn_eq_four_of_contraction K hSK hne a hcontr)











theorem gbe_unitCell_totalTurn_eq_four :
    totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 4 ∨
      totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 :=
  unitCell_turningIsFullRevolution



theorem gbe_domino_totalTurn_eq_four :
    totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = 4 ∨
      totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = -4 :=
  domino_turningIsFullRevolution





theorem gbe_unitCell_balanceIsFour : BalanceIsFour unitCell ucBase :=
  unitCell_balanceIsFour










































end Lattice

end StatMech
