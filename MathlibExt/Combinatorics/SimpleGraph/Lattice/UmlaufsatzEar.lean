/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ExtremeCell

/-!
# Partial turning sums along a boundary orbit

For a set `K` of sites of `ℤ²` and a dart `e`, the window turn `umEar_windowTurn K e a b` is the
sum of the quarter turns `turnZ` at the darts `a, a + 1, …, b - 1` of the boundary orbit of `e`.
The total turn over a period splits into window turns. When an ear is cut off, the boundary orbit
of the smaller set agrees with the old one after an initial window; the total turn is then
preserved exactly when the two initial windows have the same turn, equivalently the same
difference of right and left corners.

## Main definitions

* `StatMech.Lattice.umEar_windowTurn K e a b`: the sum of the turns at positions `a ≤ i < b` of
  the orbit of `e`.
* `StatMech.Lattice.umEar_windowRight`, `StatMech.Lattice.umEar_windowLeft`: the numbers of right
  and left corners in such a window.

## Main results

* `StatMech.Lattice.umEar_totalTurnZ_split`: the total turn splits at any intermediate position.
* `StatMech.Lattice.umEar_contraction_turning_change`: if two orbits agree after initial windows,
  their total turns differ by the difference of the initial window turns.
* `StatMech.Lattice.umEar_contraction_preserves_turning`,
  `StatMech.Lattice.umEar_contraction_preserves_turning_balance`: equal initial window turns give
  equal total turns.
* `StatMech.Lattice.umEar_extremeCell_one_le_windowLeft`: an ear at an extreme cell starts with a
  left corner.
-/

@[expose] public section

open SimpleGraph Function

namespace StatMech

namespace Lattice

/-- The sum of the quarter turns `turnZ K` at the darts `(dartNext K)^[i] e` for `a ≤ i < b`. -/
noncomputable def umEar_windowTurn (K : Set (Site 2)) (e : Dart) (a b : ℕ) : ℤ :=
  ∑ i ∈ Finset.Ico a b, turnZ K ((dartNext K)^[i] e)

@[simp] theorem umEar_windowTurn_self (K : Set (Site 2)) (e : Dart) (a : ℕ) :
    umEar_windowTurn K e a a = 0 := by
  unfold umEar_windowTurn; rw [Finset.Ico_self, Finset.sum_empty]

/-- Window turns add over consecutive windows. -/
theorem umEar_windowTurn_add (K : Set (Site 2)) (e : Dart) (a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) :
    umEar_windowTurn K e a c = umEar_windowTurn K e a b + umEar_windowTurn K e b c := by
  unfold umEar_windowTurn
  rw [← Finset.sum_Ico_consecutive _ hab hbc]

/-- The total turn over `p` steps is the window turn over `[0, p)`. -/
theorem umEar_totalTurnZ_eq_window (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    totalTurnZ K e p = umEar_windowTurn K e 0 p := by
  unfold totalTurnZ umEar_windowTurn
  rw [Finset.range_eq_Ico]

/-- The total turn over `p` steps splits at any `m ≤ p` into two window turns. -/
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

/-- Two orbits whose turns agree step by step after positions `m` and `m'` have the same window
turn over the next `n` steps. -/
theorem umEar_tail_turn_eq (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e')) :
    umEar_windowTurn K e m (m + n) = umEar_windowTurn K' e' m' (m' + n) := by
  rw [umEar_windowTurn_eq_range, umEar_windowTurn_eq_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  exact hmatch i hi

/-- If the orbits of `e` in `K` and of `e'` in `K'` have the same turns after positions `m` and
`m'` for `n` steps, their total turns over `m + n` and `m' + n` steps differ by the difference of
the initial window turns. -/
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

/-- If two orbits agree after initial windows and the initial windows have the same turn, the total
turns agree. -/
theorem umEar_contraction_preserves_turning (K K' : Set (Site 2)) (e e' : Dart)
    (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : umEar_windowTurn K' e' 0 m' = umEar_windowTurn K e 0 m) :
    totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) := by
  rw [umEar_contraction_turning_change K K' e e' m m' n hmatch, hbal]
  ring

/-- The number of right corners (turn `1`) at positions `a ≤ i < b` of the orbit of `e`. -/
noncomputable def umEar_windowRight (K : Set (Site 2)) (e : Dart) (a b : ℕ) : ℤ := by
  classical
  exact (((Finset.Ico a b).filter (fun i => turnZ K ((dartNext K)^[i] e) = 1)).card : ℤ)

/-- The number of left corners (turn `-1`) at positions `a ≤ i < b` of the orbit of `e`. -/
noncomputable def umEar_windowLeft (K : Set (Site 2)) (e : Dart) (a b : ℕ) : ℤ := by
  classical
  exact (((Finset.Ico a b).filter (fun i => turnZ K ((dartNext K)^[i] e) = -1)).card : ℤ)

/-- The window turn is the number of right corners minus the number of left corners in the window.
-/
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

/-- Version of `umEar_contraction_preserves_turning` with the initial windows compared by their
corner counts. -/
theorem umEar_contraction_preserves_turning_balance (K K' : Set (Site 2)) (e e' : Dart)
    (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : umEar_windowRight K' e' 0 m' - umEar_windowLeft K' e' 0 m' =
            umEar_windowRight K e 0 m - umEar_windowLeft K e 0 m) :
    totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) := by
  apply umEar_contraction_preserves_turning K K' e e' m m' n hmatch
  rw [umEar_windowTurn_eq_balance K' e' 0 m', umEar_windowTurn_eq_balance K e 0 m, hbal]

/-- An initial window of the orbit of the left dart of an extreme cell contains at least one left
corner. -/
theorem umEar_extremeCell_one_le_windowLeft (K : Set (Site 2)) (c : Site 2)
    (hc : IsExtremeCell K c) (m : ℕ) (hm : 1 ≤ m) :
    1 ≤ umEar_windowLeft K (leftDart c) 0 m := by
  classical
  unfold umEar_windowLeft
  have hmem : 0 ∈ (Finset.Ico 0 m).filter
      (fun i => turnZ K ((dartNext K)^[i] (leftDart c)) = -1) := by
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨Nat.zero_le 0, hm⟩, extremeCell_turnZ K c hc⟩
  have : 1 ≤ ((Finset.Ico 0 m).filter
      (fun i => turnZ K ((dartNext K)^[i] (leftDart c)) = -1)).card :=
    Finset.card_pos.mpr ⟨0, hmem⟩
  exact_mod_cast this

end Lattice

end StatMech
