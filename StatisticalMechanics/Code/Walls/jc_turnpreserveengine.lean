/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Mathlib
import Code.Lattice.UmlaufsatzEar
import Code.Lattice.GaussBonnetEar

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice













noncomputable def jc_windowTurn (K : Set (Site 2)) (e : Dart) (a b : ℕ) : ℤ :=
  umEar_windowTurn K e a b


theorem jc_windowTurn_eq (K : Set (Site 2)) (e : Dart) (a b : ℕ) :
    jc_windowTurn K e a b = umEar_windowTurn K e a b := rfl






theorem jc_totalTurnZ_split (K : Set (Site 2)) (e : Dart) (m p : ℕ) (hm : m ≤ p) :
    totalTurnZ K e p = jc_windowTurn K e 0 m + jc_windowTurn K e m p :=
  umEar_totalTurnZ_split K e m p hm












theorem jc_tail_turn_eq (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
    jc_windowTurn K e m (m + n) = jc_windowTurn K' e' m' (m' + n) :=
  umEar_tail_turn_eq K K' e e' m m' n hmatch



















theorem jc_contraction_turning_change (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
    totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) +
      (jc_windowTurn K' e' 0 m' - jc_windowTurn K e 0 m) :=
  umEar_contraction_turning_change K K' e e' m m' n hmatch




























theorem jc_ear_step_preserves_turn (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : jc_windowTurn K' e' 0 m' = jc_windowTurn K e 0 m) :
    totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) :=
  umEar_contraction_preserves_turning K K' e e' m m' n hmatch hbal








theorem jc_ear_step_preserves_turn_balance (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : umEar_windowRight K' e' 0 m' - umEar_windowLeft K' e' 0 m' =
            umEar_windowRight K e 0 m - umEar_windowLeft K e 0 m) :
    totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) :=
  umEar_contraction_preserves_turning_balance K K' e e' m m' n hmatch hbal










theorem jc_ear_step_preserves_turn_period (K K' : Set (Site 2)) (e e' : Dart) (m m' n p p' : ℕ)
    (hp : p = m + n) (hp' : p' = m' + n)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : jc_windowTurn K' e' 0 m' = jc_windowTurn K e 0 m) :
    totalTurnZ K' e' p' = totalTurnZ K e p := by
  subst hp hp'
  exact jc_ear_step_preserves_turn K K' e e' m m' n hmatch hbal











theorem jc_ear_step_eq_gbe (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : umEar_windowTurn K' e' 0 m' = umEar_windowTurn K e 0 m) :
    jc_ear_step_preserves_turn K K' e e' m m' n hmatch hbal =
      gbe_ear_step_preserves_turn K K' e e' m m' n hmatch hbal := rfl














theorem jc_domino_contracts_to_unitCell :
    totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) =
      totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) := by
  rw [show (ucBase).1 = ucDart0 from rfl, show (dmBase).1 = dmD0 from rfl,
    unitCell_orbitPeriod_eq_four, domino_orbitPeriod_eq_six]
  exact umEar_domino_contracts_to_unitCell.symm

end Walls

end StatMech
