/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Scheduling.ProjectNetwork.UniformTickCalendar
public import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Uniform tick calendar checks

Concrete consumers of `CSLibExt.Scheduling.ProjectNetwork.UniformTickCalendar` on the owner
four-job table `0 → 2, 1 → 2, 1 → 3` with durations `(3, 5, 2, 4)`: a nonunit tick length and a
nonzero epoch in hours, half-day ticks in `ℚ`, the empty table, a zero-duration milestone, and
the invalid controls (zero and negative tick lengths, a five-day working week, mixed units).
Elaboration checks, not results.
-/

namespace CSLibExtTest.Scheduling.ProjectNetwork

open Cslib.Scheduling.ProjectNetwork MathlibExt.Combinatorics.Graph.ArcNetwork

/-- The four-job precedence table `0 → 2, 1 → 2, 1 → 3`. -/
private def g4 : Digraph (Fin 4) where
  Adj i j := (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3)

private theorem g4_feasible : IsPrecedenceFeasible g4 ![3, 5, 2, 4] ![0, 0, 5, 5] := by
  intro i j h
  simp only [g4] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

private theorem g4_finish : projectFinish ![3, 5, 2, 4] ![0, 0, 5, 5] = 9 := by decide

/-- Nonunit tick length `8` h and nonzero epoch `100` h: the physical precedence
inequalities of the feasible starts (physical starts 100, 100, 140, 140). -/
example : ∀ ⦃i j⦄, g4.Adj i j →
    tickToTime (100 : ℝ) 8 (![0, 0, 5, 5] i) + (![3, 5, 2, 4] i) • (8 : ℝ) ≤
      tickToTime 100 8 (![0, 0, 5, 5] j) :=
  (isPrecedenceFeasible_iff_tickToTime (100 : ℝ) (by norm_num)).mp g4_feasible

/-- The physical project finish is `172` h. -/
example : IsLeast {t : ℝ | 100 ≤ t ∧
    ∀ j, tickToTime 100 8 (![0, 0, 5, 5] j) + (![3, 5, 2, 4] j) • (8 : ℝ) ≤ t} 172 := by
  have h := isLeast_tickToTime_projectFinish ![3, 5, 2, 4] ![0, 0, 5, 5] (100 : ℝ) (L := 8)
    (by norm_num)
  rwa [g4_finish, show tickToTime (100 : ℝ) 8 9 = 172 by norm_num [tickToTime]] at h

/-- The owner critical-path bound in physical time: chain `[1, 3]` (9 ticks, 72 h) ends no
earlier than the physical project finish allows, tight at `100 + 72 = 172`. -/
example : tickToTime (100 : ℝ) 8 0 + 9 • (8 : ℝ) ≤
    tickToTime 100 8 (projectFinish ![3, 5, 2, 4] ![0, 0, 5, 5]) := by
  have hc : ([1, 3] : List (Fin 4)).IsChain g4.Adj := by simp [List.isChain_cons, g4]
  have h := sum_map_le_projectFinish g4_feasible hc
  exact (tickToTime_add_nsmul_le_tickToTime_iff (100 : ℝ) (by norm_num)).mpr
    (by simpa using h)

/-- The split network in physical time: every arc's physical inequality holds, the source
event is at the epoch and the sink event at `172` h. -/
example : (∀ e, tickToTime (100 : ℝ) 8 (embedSchedule ![3, 5, 2, 4] ![0, 0, 5, 5]
      (splitTail g4 e)) + splitDuration g4 ![3, 5, 2, 4] e • (8 : ℝ) ≤
      tickToTime 100 8 (embedSchedule ![3, 5, 2, 4] ![0, 0, 5, 5] (splitHead g4 e))) ∧
    tickToTime (100 : ℝ) 8 (embedSchedule ![3, 5, 2, 4] ![0, 0, 5, 5] .source) = 100 ∧
    tickToTime (100 : ℝ) 8 (embedSchedule ![3, 5, 2, 4] ![0, 0, 5, 5] .sink) = 172 := by
  refine ⟨(isFeasibleSchedule_iff_tickToTime (100 : ℝ) (by norm_num)).mp
    (isFeasibleSchedule_embedSchedule g4_feasible), ?_, ?_⟩
  · simp [embedSchedule, tickToTime]
  · rw [show embedSchedule ![3, 5, 2, 4] ![0, 0, 5, 5] .sink = 9 from g4_finish]
    norm_num [tickToTime]

/-- Half-day ticks from day `7` in `ℚ`. -/
example : tickToTime (7 : ℚ) (1 / 2) 4 = 9 ∧ StrictMono (tickToTime (7 : ℚ) (1 / 2)) :=
  ⟨by norm_num [tickToTime], tickToTime_strictMono 7 (by norm_num)⟩

/-- Empty job table: project finish `0`, physical finish the epoch. -/
example : IsLeast {t : ℝ | 100 ≤ t ∧ ∀ j : Empty,
    tickToTime 100 8 (j.elim : ℕ) + (j.elim : ℕ) • (8 : ℝ) ≤ t} 100 := by
  have h := isLeast_tickToTime_projectFinish (fun x : Empty => (x.elim : ℕ))
    (fun x : Empty => (x.elim : ℕ)) (100 : ℝ) (L := 8) (by norm_num)
  rwa [show tickToTime (100 : ℝ) 8 (projectFinish (fun x : Empty => (x.elim : ℕ))
    (fun x : Empty => (x.elim : ℕ))) = 100 by simp [tickToTime, projectFinish]] at h

/-- Zero-duration milestone (chain `0 → 1 → 2`, durations `(4, 0, 3)`, starts `(0, 4, 4)`):
the milestone finishes when it starts, and the physical project finish is `156` h. -/
example : tickToTime (100 : ℝ) 8 4 + (0 : ℕ) • (8 : ℝ) = tickToTime 100 8 4 ∧
    IsLeast {t : ℝ | 100 ≤ t ∧
      ∀ j, tickToTime 100 8 (![0, 4, 4] j) + (![4, 0, 3] j) • (8 : ℝ) ≤ t} 156 := by
  refine ⟨by simp, ?_⟩
  have h := isLeast_tickToTime_projectFinish ![4, 0, 3] ![0, 4, 4] (100 : ℝ) (L := 8)
    (by norm_num)
  rwa [show projectFinish ![4, 0, 3] ![0, 4, 4] = 7 by decide,
    show tickToTime (100 : ℝ) 8 7 = 156 by norm_num [tickToTime]] at h

/-- The tight pair `1 → 2` maps to a physical equality, and a grid instant determines its
tick. -/
example : tickToTime (100 : ℝ) 8 0 + 5 • (8 : ℝ) = tickToTime 100 8 5 ∧
    ∀ a b : ℕ, tickToTime (100 : ℝ) 8 a = tickToTime 100 8 b → a = b :=
  ⟨by norm_num [tickToTime], fun _ _ h => (tickToTime_strictMono (100 : ℝ) (by norm_num)).injective h⟩

/-- Zero tick length: infeasible starts `(0, 0, 4, 5)` satisfy every physical inequality,
and the conversion is not injective. -/
example : (¬ IsPrecedenceFeasible g4 ![3, 5, 2, 4] ![0, 0, 4, 5]) ∧ (∀ ⦃i j⦄, g4.Adj i j →
    tickToTime (100 : ℝ) 0 (![0, 0, 4, 5] i) + (![3, 5, 2, 4] i) • (0 : ℝ) ≤
      tickToTime 100 0 (![0, 0, 4, 5] j)) ∧ ¬ StrictMono (tickToTime (100 : ℝ) 0) := by
  refine ⟨fun h => ?_, fun _ _ _ => by simp [tickToTime], fun h => ?_⟩
  · have := @h 1 2 (by simp [g4])
    simp at this
  · have := h (show (0 : ℕ) < 1 by norm_num)
    simp [tickToTime] at this

/-- Negative tick length: the feasible pair `0 → 2` maps to `97 ≤ 95`, and one job of
duration `1` from tick `0` finishes physically before the epoch. -/
example : (¬ ∀ ⦃i j⦄, g4.Adj i j →
      tickToTime (100 : ℝ) (-1) (![0, 0, 5, 5] i) + (![3, 5, 2, 4] i) • (-1 : ℝ) ≤
        tickToTime 100 (-1) (![0, 0, 5, 5] j)) ∧
    ¬ IsLeast {t : ℝ | 0 ≤ t ∧ ∀ j : Unit,
      tickToTime 0 (-1) ((fun _ : Unit => 0) j) + (fun _ : Unit => 1) j • (-1 : ℝ) ≤ t}
      (tickToTime 0 (-1) (projectFinish (fun _ : Unit => 1) (fun _ => 0))) := by
  refine ⟨fun h => ?_, ?_⟩
  · have := @h 0 2 (by simp [g4])
    norm_num [tickToTime] at this
  · rintro ⟨⟨h0, -⟩, -⟩
    rw [show projectFinish (fun _ : Unit => 1) (fun _ => 0) = 1 by decide] at h0
    norm_num [tickToTime] at h0

/-- A five-day working week (working day `n` starts on calendar day `n + 2 * (n / 5)`) is
not a uniform calendar: it is of no `tickToTime` form, elapsed calendar time depends on the
start, and a tick count compared with hours gives the wrong answer. -/
example : (¬ ∃ t₀ L : ℝ, ∀ n : ℕ, ((n + 2 * (n / 5) : ℕ) : ℝ) = tickToTime t₀ L n) ∧
    (4 + 1) + 2 * ((4 + 1) / 5) ≠ (4 + 2 * (4 / 5)) + 1 ∧
    ((9 : ℕ) : ℝ) ≤ 100 ∧ ¬ (tickToTime (100 : ℝ) 8 9 ≤ 100) := by
  refine ⟨?_, by decide, by norm_num, by norm_num [tickToTime]⟩
  rintro ⟨t₀, L, h⟩
  have h0 := h 0
  have h1 := h 1
  have h5 := h 5
  simp [tickToTime] at h0 h1 h5
  linarith

end CSLibExtTest.Scheduling.ProjectNetwork

#print axioms Cslib.Scheduling.ProjectNetwork.tickToTime_add
#print axioms Cslib.Scheduling.ProjectNetwork.tickToTime_strictMono
#print axioms Cslib.Scheduling.ProjectNetwork.tickToTime_add_nsmul_le_tickToTime_iff
#print axioms Cslib.Scheduling.ProjectNetwork.isFeasibleSchedule_iff_tickToTime
#print axioms Cslib.Scheduling.ProjectNetwork.isPrecedenceFeasible_iff_tickToTime
#print axioms Cslib.Scheduling.ProjectNetwork.isLeast_tickToTime_projectFinish
