/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Mathlib
import Code.Walls.jc_turnpreserveengine
import Code.Lattice.UmlaufsatzEar
import Code.Lattice.GaussBonnetEar
import Code.Lattice.BalancePreservingContraction

open SimpleGraph Function

namespace StatMech

namespace Walls

open StatMech.Lattice











theorem jc2_windowTurn_eq (K : Set (Site 2)) (e : Dart) (a b : ℕ) :
    jc_windowTurn K e a b = umEar_windowTurn K e a b :=
  jc_windowTurn_eq K e a b




theorem jc2_totalTurnZ_split (K : Set (Site 2)) (e : Dart) (m p : ℕ) (hm : m ≤ p) :
    totalTurnZ K e p = jc_windowTurn K e 0 m + jc_windowTurn K e m p :=
  jc_totalTurnZ_split K e m p hm










theorem jc2_tail_turn_eq (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
    jc_windowTurn K e m (m + n) = jc_windowTurn K' e' m' (m' + n) :=
  jc_tail_turn_eq K K' e e' m m' n hmatch










theorem jc2_contraction_turning_change (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
    totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) +
      (jc_windowTurn K' e' 0 m' - jc_windowTurn K e 0 m) :=
  jc_contraction_turning_change K K' e e' m m' n hmatch



























theorem jc2_engine (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : jc_windowTurn K' e' 0 m' = jc_windowTurn K e 0 m) :
    totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) :=
  jc_ear_step_preserves_turn K K' e e' m m' n hmatch hbal






theorem jc2_engine_period (K K' : Set (Site 2)) (e e' : Dart) (m m' n p p' : ℕ)
    (hp : p = m + n) (hp' : p' = m' + n)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : jc_windowTurn K' e' 0 m' = jc_windowTurn K e 0 m) :
    totalTurnZ K' e' p' = totalTurnZ K e p :=
  jc_ear_step_preserves_turn_period K K' e e' m m' n p p' hp hp' hmatch hbal






theorem jc2_engine_balance (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : umEar_windowRight K' e' 0 m' - umEar_windowLeft K' e' 0 m' =
            umEar_windowRight K e 0 m - umEar_windowLeft K e 0 m) :
    totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) :=
  jc_ear_step_preserves_turn_balance K K' e e' m m' n hmatch hbal










theorem jc2_engine_eq_turnPreserveEngine (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : jc_windowTurn K' e' 0 m' = jc_windowTurn K e 0 m) :
    jc2_engine K K' e e' m m' n hmatch hbal =
      jc_ear_step_preserves_turn K K' e e' m m' n hmatch hbal := rfl















theorem jc2_engine_saturating_pos (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : jc_windowTurn K' e' 0 m' = jc_windowTurn K e 0 m)
    (hval : totalTurnZ K e (m + n) = 4) :
    totalTurnZ K' e' (m' + n) = 4 := by
  rw [jc2_engine K K' e e' m m' n hmatch hbal, hval]





theorem jc2_engine_saturating_neg (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : jc_windowTurn K' e' 0 m' = jc_windowTurn K e 0 m)
    (hval : totalTurnZ K e (m + n) = -4) :
    totalTurnZ K' e' (m' + n) = -4 := by
  rw [jc2_engine K K' e e' m m' n hmatch hbal, hval]






theorem jc2_engine_saturating_full_revolution (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : jc_windowTurn K' e' 0 m' = jc_windowTurn K e 0 m)
    (hval : totalTurnZ K e (m + n) = 4 ∨ totalTurnZ K e (m + n) = -4) :
    totalTurnZ K' e' (m' + n) = 4 ∨ totalTurnZ K' e' (m' + n) = -4 := by
  rcases hval with h | h
  · exact Or.inl (jc2_engine_saturating_pos K K' e e' m m' n hmatch hbal h)
  · exact Or.inr (jc2_engine_saturating_neg K K' e e' m m' n hmatch hbal h)















theorem jc2_domino_contracts_to_unitCell :
    totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) =
      totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) :=
  jc_domino_contracts_to_unitCell





theorem jc2_domino_unitCell_saturating_value :
    totalTurnZ domino dmD0 6 = -4 ∧ totalTurnZ unitCell ucDart0 4 = -4 :=
  umEar_domino_unitCell_totalTurnZ

end Walls

end StatMech
