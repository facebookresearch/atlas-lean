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

open SimpleGraph Function

namespace StatMech

namespace Lattice












noncomputable def umEar_windowTurn (K : Set (Site 2)) (e : Dart) (a b : ℕ) : ℤ :=
  ∑ i ∈ Finset.Ico a b, turnZ K ((dartNext K)^[i] e)


@[simp] theorem umEar_windowTurn_self (K : Set (Site 2)) (e : Dart) (a : ℕ) :
    umEar_windowTurn K e a a = 0 := by
  unfold umEar_windowTurn; rw [Finset.Ico_self, Finset.sum_empty]




theorem umEar_windowTurn_add (K : Set (Site 2)) (e : Dart) (a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) :
    umEar_windowTurn K e a c = umEar_windowTurn K e a b + umEar_windowTurn K e b c := by
  unfold umEar_windowTurn
  rw [← Finset.sum_Ico_consecutive _ hab hbc]


theorem umEar_totalTurnZ_eq_window (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    totalTurnZ K e p = umEar_windowTurn K e 0 p := by
  unfold totalTurnZ umEar_windowTurn
  rw [Finset.range_eq_Ico]





theorem umEar_totalTurnZ_split (K : Set (Site 2)) (e : Dart) (m p : ℕ) (hm : m ≤ p) :
    totalTurnZ K e p = umEar_windowTurn K e 0 m + umEar_windowTurn K e m p := by
  rw [umEar_totalTurnZ_eq_window]
  exact umEar_windowTurn_add K e 0 m p (Nat.zero_le m) hm




theorem umEar_windowTurn_eq_range (K : Set (Site 2)) (e : Dart) (a n : ℕ) :
    umEar_windowTurn K e a (a + n) =
      ∑ i ∈ Finset.range n, turnZ K ((dartNext K)^[a + i] e) := by
  unfold umEar_windowTurn
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr (by rw [Nat.add_sub_cancel_left])
  intro i _
  rw [Nat.add_comm a i]














theorem umEar_tail_turn_eq (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
    umEar_windowTurn K e m (m + n) = umEar_windowTurn K' e' m' (m' + n) := by
  rw [umEar_windowTurn_eq_range, umEar_windowTurn_eq_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  exact hmatch i hi























theorem umEar_contraction_turning_change (K K' : Set (Site 2)) (e e' : Dart)
    (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
    totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) +
      (umEar_windowTurn K' e' 0 m' - umEar_windowTurn K e 0 m) := by
  have htail := umEar_tail_turn_eq K K' e e' m m' n hmatch
  rw [umEar_totalTurnZ_split K e m (m + n) (Nat.le_add_right m n),
      umEar_totalTurnZ_split K' e' m' (m' + n) (Nat.le_add_right m' n),
      htail]
  ring




















theorem umEar_contraction_preserves_turning (K K' : Set (Site 2)) (e e' : Dart)
    (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : umEar_windowTurn K' e' 0 m' = umEar_windowTurn K e 0 m) :
    totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) := by
  rw [umEar_contraction_turning_change K K' e e' m m' n hmatch, hbal]
  ring










noncomputable def umEar_windowRight (K : Set (Site 2)) (e : Dart) (a b : ℕ) : ℤ := by
  classical
  exact (((Finset.Ico a b).filter (fun i => turnZ K ((dartNext K)^[i] e) = 1)).card : ℤ)



noncomputable def umEar_windowLeft (K : Set (Site 2)) (e : Dart) (a b : ℕ) : ℤ := by
  classical
  exact (((Finset.Ico a b).filter (fun i => turnZ K ((dartNext K)^[i] e) = -1)).card : ℤ)




theorem umEar_windowTurn_eq_balance (K : Set (Site 2)) (e : Dart) (a b : ℕ) :
    umEar_windowTurn K e a b = umEar_windowRight K e a b - umEar_windowLeft K e a b := by
  classical
  unfold umEar_windowTurn umEar_windowRight umEar_windowLeft
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases turnZ_mem K ((dartNext K)^[i] e) with h | h | h <;> rw [h] <;> norm_num







theorem umEar_contraction_preserves_turning_balance (K K' : Set (Site 2)) (e e' : Dart)
    (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : umEar_windowRight K' e' 0 m' - umEar_windowLeft K' e' 0 m' =
            umEar_windowRight K e 0 m - umEar_windowLeft K e 0 m) :
    totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) := by
  apply umEar_contraction_preserves_turning K K' e e' m m' n hmatch
  rw [umEar_windowTurn_eq_balance K' e' 0 m', umEar_windowTurn_eq_balance K e 0 m, hbal]















theorem umEar_extremeCell_ear_first_turn (K : Set (Site 2)) (c : Site 2)
    (hc : IsExtremeCell K c) :
    turnZ K ((dartNext K)^[0] (leftDart c)) = -1 := by
  rw [Function.iterate_zero_apply]
  exact extremeCell_turnZ K c hc





theorem umEar_extremeCell_one_le_windowLeft (K : Set (Site 2)) (c : Site 2)
    (hc : IsExtremeCell K c) (m : ℕ) (hm : 1 ≤ m) :
    1 ≤ umEar_windowLeft K (leftDart c) 0 m := by
  classical
  unfold umEar_windowLeft
  have hmem : 0 ∈ (Finset.Ico 0 m).filter
      (fun i => turnZ K ((dartNext K)^[i] (leftDart c)) = -1) := by
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨Nat.zero_le 0, hm⟩, umEar_extremeCell_ear_first_turn K c hc⟩
  have : 1 ≤ ((Finset.Ico 0 m).filter
      (fun i => turnZ K ((dartNext K)^[i] (leftDart c)) = -1)).card :=
    Finset.card_pos.mpr ⟨0, hmem⟩
  exact_mod_cast this


















theorem umEar_domino_contracts_to_unitCell :
    totalTurnZ domino dmD0 6 = totalTurnZ unitCell ucDart0 4 := by
  rw [domino_totalTurnZ_six, unitCell_totalTurnZ_four]






theorem umEar_domino_unitCell_totalTurnZ :
    totalTurnZ domino dmD0 6 = -4 ∧ totalTurnZ unitCell ucDart0 4 = -4 :=
  ⟨domino_totalTurnZ_six, unitCell_totalTurnZ_four⟩

end Lattice

end StatMech
