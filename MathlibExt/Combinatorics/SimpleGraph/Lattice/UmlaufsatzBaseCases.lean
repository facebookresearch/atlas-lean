/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CornerBalanceDomino

/-!
# Turning angles and the base cases of the lattice Umlaufsatz

The quarter turn `turnZ K e ∈ {1, 0, -1}` at a boundary dart is read as the signed angle
`turnZ K e · π/2`, and the total turning angle of a boundary orbit is the sum of these angles. The
three cases of the successor rule fix both the turn and the new direction. For the unit cell
(one site) and the horizontal domino (two sites), the boundary orbits have four and six darts,
four corners of the same kind and no corners of the other kind, and total turning angle `-2π`:
one full clockwise revolution.

## Main definitions

* `StatMech.Lattice.turnAngle K e`: the signed turning angle `turnZ K e · π/2` at `e`.
* `StatMech.Lattice.totalTurnAngle K e p`: the sum of the turning angles over `p` steps of the
  orbit of `e`.

## Main results

* `StatMech.Lattice.umBase_turnZ_right_iff`, `StatMech.Lattice.umBase_turnZ_left_iff`,
  `StatMech.Lattice.umBase_turnZ_straight_iff`: the turn and the new direction in each case of the
  successor rule.
* `StatMech.Lattice.umBase_totalTurnAngle_eq`: total turning angle = total turn `· π/2`.
* `StatMech.Lattice.umBase_square_turning`, `StatMech.Lattice.umBase_domino_turning`: the unit cell
  and the domino have total turning angle `-2π`.
* `StatMech.Lattice.umBase_cornerBalance`, `StatMech.Lattice.umBase_domino_cornerBalance`: their
  corner counts differ by four.
-/

@[expose] public section

open SimpleGraph Function

namespace StatMech

namespace Lattice

/-- If the site diagonally ahead of `e` lies in `K`, the turn at `e` is `1` and the successor
direction is `e.dir` rotated by a quarter turn. -/
theorem umBase_turnZ_right_iff (K : Set (Site 2)) (e : Dart)
    (h : e.head + (-rot90Fun e.dir) ∈ K) :
    turnZ K e = 1 ∧ (dartNext K e).dir = rot90Fun e.dir := by
  classical
  refine ⟨?_, (dartNext_front_head K e h).2⟩
  unfold turnZ; rw [ite_eq_left h]

/-- If neither probed site lies in `K`, the turn at `e` is `-1` and the successor direction is
`e.dir` rotated by a quarter turn the other way. -/
theorem umBase_turnZ_left_iff (K : Set (Site 2)) (e : Dart)
    (h1 : e.head + (-rot90Fun e.dir) ∉ K) (h2 : e.tail + (-rot90Fun e.dir) ∉ K) :
    turnZ K e = -1 ∧ (dartNext K e).dir = -rot90Fun e.dir := by
  classical
  refine ⟨?_, dartNext_left_dir K e h1 h2⟩
  unfold turnZ; rw [ite_eq_right h1, ite_eq_right h2]

/-- If only the site beside the tail of `e` lies in `K`, the turn at `e` is `0` and the direction
is unchanged. -/
theorem umBase_turnZ_straight_iff (K : Set (Site 2)) (e : Dart)
    (h1 : e.head + (-rot90Fun e.dir) ∉ K) (h2 : e.tail + (-rot90Fun e.dir) ∈ K) :
    turnZ K e = 0 ∧ (dartNext K e).dir = e.dir := by
  classical
  refine ⟨?_, dartNext_straight_dir K e h1 h2⟩
  unfold turnZ; rw [ite_eq_right h1, ite_eq_left h2]

open Real in
/-- The signed turning angle `turnZ K e · π/2` at the dart `e`: `π/2`, `0` or `-π/2`. -/
noncomputable def turnAngle (K : Set (Site 2)) (e : Dart) : ℝ :=
  (turnZ K e : ℝ) * (Real.pi / 2)

open Real in
/-- The turning angle at a dart is `π/2`, `0` or `-π/2`. -/
theorem umBase_turnAngle_mem (K : Set (Site 2)) (e : Dart) :
    turnAngle K e = Real.pi / 2 ∨ turnAngle K e = 0 ∨ turnAngle K e = -(Real.pi / 2) := by
  unfold turnAngle
  rcases turnZ_mem K e with h | h | h <;> rw [h]
  · left; push_cast; ring
  · right; left; push_cast; ring
  · right; right; push_cast; ring

open Real in
/-- Each turning angle has absolute value at most `π/2`. -/
theorem umBase_abs_turnAngle_le (K : Set (Site 2)) (e : Dart) :
    |turnAngle K e| ≤ Real.pi / 2 := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rcases umBase_turnAngle_mem K e with h | h | h <;> rw [h]
  · rw [abs_of_nonneg hpi]
  · simpa using hpi
  · rw [abs_neg, abs_of_nonneg hpi]

open Real in
/-- The total turning angle of the first `p` steps of the boundary orbit of `e`. -/
noncomputable def totalTurnAngle (K : Set (Site 2)) (e : Dart) (p : ℕ) : ℝ :=
  ∑ i ∈ Finset.range p, turnAngle K ((dartNext K)^[i] e)

open Real in
/-- The total turning angle is the total turn `totalTurnZ K e p` times `π/2`. -/
theorem umBase_totalTurnAngle_eq (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    totalTurnAngle K e p = (totalTurnZ K e p : ℝ) * (Real.pi / 2) := by
  unfold totalTurnAngle turnAngle totalTurnZ
  rw [← Finset.sum_mul]
  push_cast
  rfl

open Real in
/-- The boundary orbit of the unit cell has total turning angle `-2π`. -/
theorem umBase_square_turning : totalTurnAngle unitCell ucDart0 4 = -(2 * Real.pi) := by
  rw [umBase_totalTurnAngle_eq, unitCell_totalTurnZ_four]
  push_cast
  ring

open Real in
/-- The boundary orbit of the unit cell, taken over its period, has total turning angle `-2π`. -/
theorem umBase_square_turning_period :
    totalTurnAngle unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -(2 * Real.pi) := by
  rw [show (ucBase).1 = ucDart0 from rfl, unitCell_orbitPeriod_eq_four]
  exact umBase_square_turning

/-- The unit-cell orbit has no corners with turn `1`. -/
theorem umBase_square_rightCount : rightCornerCount unitCell ucDart0 4 = 0 := by
  classical
  unfold rightCornerCount
  rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi
  simp only [Finset.mem_range] at hi
  interval_cases i
  · rw [Function.iterate_zero_apply, ucDart0_turnZ]; decide
  · rw [iterate_ucDart_1, ucDart1_turnZ]; decide
  · rw [iterate_ucDart_2, ucDart2_turnZ]; decide
  · rw [iterate_ucDart_3, ucDart3_turnZ]; decide

/-- All four darts of the unit-cell orbit are corners with turn `-1`. -/
theorem umBase_square_leftCount : leftCornerCount unitCell ucDart0 4 = 4 := by
  classical
  unfold leftCornerCount
  have hfilter : (Finset.range 4).filter
      (fun i => turnZ unitCell ((dartNext unitCell)^[i] ucDart0) = -1) = Finset.range 4 := by
    rw [Finset.filter_eq_self]
    intro i hi
    simp only [Finset.mem_range] at hi
    interval_cases i
    · rw [Function.iterate_zero_apply]; exact ucDart0_turnZ
    · rw [iterate_ucDart_1]; exact ucDart1_turnZ
    · rw [iterate_ucDart_2]; exact ucDart2_turnZ
    · rw [iterate_ucDart_3]; exact ucDart3_turnZ
  rw [hfilter]
  simp

theorem umBase_cornerBalance :
    leftCornerCount unitCell ucDart0 4 - rightCornerCount unitCell ucDart0 4 = 4 := by
  rw [umBase_square_leftCount, umBase_square_rightCount]; ring

theorem umBase_cornerBalance_eq_neg_turnCount :
    leftCornerCount unitCell ucDart0 4 - rightCornerCount unitCell ucDart0 4
      = -(totalTurnZ unitCell ucDart0 4) := by
  rw [totalTurnZ_eq_cornerBalance]
  ring

/-- The domino orbit has no corners with turn `1`. -/
theorem umBase_domino_rightCount : rightCornerCount domino dmD0 6 = 0 := by
  classical
  unfold rightCornerCount
  rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi
  simp only [Finset.mem_range] at hi
  interval_cases i
  · rw [Function.iterate_zero_apply, dmD0_turnZ]; decide
  · rw [iterate_dmD_1, dmD1_turnZ]; decide
  · rw [iterate_dmD_2, dmD2_turnZ]; decide
  · rw [iterate_dmD_3, dmD3_turnZ]; decide
  · rw [iterate_dmD_4, dmD4_turnZ]; decide
  · rw [iterate_dmD_5, dmD5_turnZ]; decide

/-- The domino orbit has four corners with turn `-1`. -/
theorem umBase_domino_leftCount : leftCornerCount domino dmD0 6 = 4 := by
  classical
  unfold leftCornerCount
  have hcard : ((Finset.range 6).filter
      (fun i => turnZ domino ((dartNext domino)^[i] dmD0) = -1)).card = 4 := by
    rw [Finset.card_filter]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    rw [Function.iterate_zero_apply, dmD0_turnZ, iterate_dmD_1, dmD1_turnZ,
      iterate_dmD_2, dmD2_turnZ, iterate_dmD_3, dmD3_turnZ, iterate_dmD_4, dmD4_turnZ,
      iterate_dmD_5, dmD5_turnZ]
    decide
  rw [hcard]; rfl

theorem umBase_domino_cornerBalance :
    leftCornerCount domino dmD0 6 - rightCornerCount domino dmD0 6 = 4 := by
  rw [umBase_domino_leftCount, umBase_domino_rightCount]; ring

open Real in
/-- The boundary orbit of the domino has total turning angle `-2π`. -/
theorem umBase_domino_turning : totalTurnAngle domino dmD0 6 = -(2 * Real.pi) := by
  rw [umBase_totalTurnAngle_eq, domino_totalTurnZ_six]
  push_cast
  ring

end Lattice

end StatMech
