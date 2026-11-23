/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Scheduling.ProjectNetwork.JobSplitting
public import Mathlib.Algebra.Order.Monoid.Defs

import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cslib.Scheduling.ProjectNetwork

open MathlibExt.Combinatorics.Graph.ArcNetwork

/-!
# Uniform calendar: affine conversion of critical-path ticks to physical time

Ticks. Times and durations of the critical-path interface are
natural numbers of ticks, and tick `0` is the project start. An activity-on-arc network
`tail head : E → V` with arc durations `dur : E → ℕ` has the feasible event schedules
`τ : V → ℕ`, with `τ (tail e) + dur e ≤ τ (head e)` for every arc (`IsFeasibleSchedule`). A job
table with jobs `J`, durations `d : J → ℕ` and a precedence digraph `G : Digraph J`, where
`G.Adj i j` means job `i` finishes before job `j` starts (finish-to-start, zero lag), has the
precedence-feasible start ticks `s : J → ℕ`, with `s i + d i ≤ s j` whenever `G.Adj i j`
(`IsPrecedenceFeasible`). Job `j` finishes at `s j + d j`, and the project finish is the latest
job finish, `0` for an empty job type (`projectFinish`).

Physical time. Physical instants and durations lie in one type `T`, an ordered cancellative
additive commutative monoid: instants are measured from one fixed reference instant, and
instants and durations in one fixed unit; `≤` reads "no later than" on instants and "no longer
than" on durations. Only addition, the order and the multiple `n • L` of a duration by a tick
count (repeated addition) are used, so `T` may be `ℝ` or `ℚ` in hours, or `ℤ` or `ℕ` in minutes.

Uniform calendar. A fixed tick length `L : T`, the physical duration of every tick, and a fixed
epoch `t₀ : T`, the physical instant of tick `0`. Instants convert affinely, tick `n` to
`tickToTime t₀ L n = t₀ + n • L`; durations convert linearly and without the epoch, `n` ticks to
`n • L`. The conversion runs from ticks to physical time: tick counts are scaled by `L`. Every
tick has the same length and calendar time has no gaps, so elapsed physical time depends only on
elapsed ticks (`tickToTime_add`). The tick length is assumed positive where a strict comparison
or the reverse direction of an equivalence needs it; the uniform law needs no assumption on it
and the project-finish statement only `0 ≤ L`.

Main results. The uniform law. For `0 < L` the conversion is an order embedding, so comparisons
between tick instants, project finishes included, agree with the comparisons between their
physical instants. A tick inequality `a + n ≤ b` holds exactly when its physical image
`tickToTime t₀ L a + n • L ≤ tickToTime t₀ L b` holds; so feasibility of event schedules and
precedence feasibility of start ticks hold exactly when the corresponding physical inequalities
hold, for every epoch. The physical instant of the project finish is the earliest instant at or
after the epoch by which every job has finished physically: the latest physical job finish, or
the epoch for an empty job type.

Rounding and totalized operations: none. Only tick instants are converted, and a tick is
determined by its physical instant, so a physical instant on the tick grid reads back as a tick
without rounding. There is no subtraction, division or inverse.

Scope and exclusions. A uniform calendar only. A working calendar with nonworking time is not an
affine conversion and is excluded: in a five-day working week whose ticks are working days,
counted from the start of a Monday, working days `4` and `5` start three calendar days apart but
working days `0` and `1` one day apart. Also excluded: lags other than zero finish-to-start lags,
real-valued durations and a real-duration critical-path method, conversion of physical instants
off the tick grid (rounding), time zones and clock changes, and resource feasibility.
-/

/-- The physical instant of tick `n` under the uniform calendar with epoch `t₀`, the physical
instant of tick `0`, and tick length `L`, the physical duration of one tick: `t₀ + n • L`.
Instants convert affinely; a duration of `n` ticks converts linearly to `n • L`. -/
def tickToTime {T : Type*} [AddMonoid T] (t₀ L : T) (n : ℕ) : T :=
  t₀ + n • L

/-- Uniform calendar law: the physical instant `n` ticks after tick `m` is the instant of tick
`m` plus the physical duration `n • L` of `n` ticks, whatever `m` is, so elapsed physical time
depends only on elapsed ticks. The day map of a working calendar with nonworking time breaks
this law, so it is not of this form. No assumption on the tick length is needed. -/
theorem tickToTime_add {T : Type*} [AddMonoid T] (t₀ L : T) (m n : ℕ) :
    tickToTime t₀ L (m + n) = tickToTime t₀ L m + n • L := by
  unfold tickToTime
  rw [add_nsmul, add_assoc]

/-- Order embedding: for a positive tick length, a later tick is a strictly later physical
instant. Hence a comparison between tick instants, a comparison of project finishes included,
holds exactly when the comparison between their physical instants holds
(`StrictMono.le_iff_le`, `StrictMono.lt_iff_lt`), and a tick is determined by its physical
instant (`StrictMono.injective`), so a physical instant on the tick grid reads back as a tick
without rounding. -/
theorem tickToTime_strictMono {T : Type*} [AddCommMonoid T] [PartialOrder T]
    [IsOrderedCancelAddMonoid T] (t₀ : T) {L : T} (hL : 0 < L) :
    StrictMono (tickToTime t₀ L) := by
  intro m n hmn
  exact (add_lt_add_iff_left t₀).mpr (nsmul_lt_nsmul_left hL hmn)

/-- Precedence inequality in physical time: for a positive tick length, the tick inequality
`a + n ≤ b`, instant `a` plus `n` ticks no later than instant `b`, holds exactly when its
physical image holds, the instant of tick `a` plus the physical duration `n • L` no later than
the instant of tick `b`. Every precedence inequality of the critical-path interface has this
form, and so does a critical-path bound on a project finish (with `a = 0`). -/
theorem tickToTime_add_nsmul_le_tickToTime_iff {T : Type*} [AddCommMonoid T] [PartialOrder T]
    [IsOrderedCancelAddMonoid T] (t₀ : T) {L : T} (hL : 0 < L) {a n b : ℕ} :
    tickToTime t₀ L a + n • L ≤ tickToTime t₀ L b ↔ a + n ≤ b := by
  rw [← tickToTime_add]
  exact (tickToTime_strictMono t₀ hL).le_iff_le

/-- Feasible event schedules in physical time, activity-on-arc form: for a positive tick length,
event ticks `τ` are a feasible schedule exactly when, in physical time, the head event of every
arc occurs no earlier than its tail event plus the arc's physical duration `dur e • L`. This
holds for every epoch. -/
theorem isFeasibleSchedule_iff_tickToTime {T : Type*} [AddCommMonoid T] [PartialOrder T]
    [IsOrderedCancelAddMonoid T] {V E : Type*} {tail head : E → V} {dur : E → ℕ} {τ : V → ℕ}
    (t₀ : T) {L : T} (hL : 0 < L) :
    IsFeasibleSchedule tail head dur τ ↔
      ∀ e, tickToTime t₀ L (τ (tail e)) + dur e • L ≤ tickToTime t₀ L (τ (head e)) := by
  constructor
  · intro h e
    exact (tickToTime_add_nsmul_le_tickToTime_iff t₀ hL).mpr (h e)
  · intro h e
    exact (tickToTime_add_nsmul_le_tickToTime_iff t₀ hL).mp (h e)

/-- Precedence feasibility in physical time, job-table form: for a positive tick length, start
ticks `s` are precedence-feasible exactly when, in physical time, every job starts no earlier
than each of its predecessors `i` finishes, at the physical start of `i` plus its physical
duration `d i • L`. This is the physical-to-canonical bridge for start instants on the tick
grid, for every epoch. -/
theorem isPrecedenceFeasible_iff_tickToTime {T : Type*} [AddCommMonoid T] [PartialOrder T]
    [IsOrderedCancelAddMonoid T] {J : Type*} {G : Digraph J} {d s : J → ℕ} (t₀ : T) {L : T}
    (hL : 0 < L) :
    IsPrecedenceFeasible G d s ↔
      ∀ ⦃i j⦄, G.Adj i j → tickToTime t₀ L (s i) + d i • L ≤ tickToTime t₀ L (s j) := by
  constructor
  · intro h i j hij
    exact (tickToTime_add_nsmul_le_tickToTime_iff t₀ hL).mpr (h hij)
  · intro h i j hij
    exact (tickToTime_add_nsmul_le_tickToTime_iff t₀ hL).mp (h hij)

/-- Physical project finish: for a nonnegative tick length, the physical instant of the project
finish is the earliest instant, no earlier than the epoch, by which every job `j` has finished
physically, at its physical start plus its physical duration, `tickToTime t₀ L (s j) + d j • L`.
For a nonempty job type it is therefore the latest physical job finish, and for an empty job type
it is the epoch. -/
theorem isLeast_tickToTime_projectFinish {T : Type*} [AddCommMonoid T] [PartialOrder T]
    [IsOrderedCancelAddMonoid T] {J : Type*} [Fintype J] (d s : J → ℕ) (t₀ : T) {L : T}
    (hL : 0 ≤ L) :
    IsLeast {t | t₀ ≤ t ∧ ∀ j, tickToTime t₀ L (s j) + d j • L ≤ t}
      (tickToTime t₀ L (projectFinish d s)) := by
  constructor
  · constructor
    · show t₀ ≤ t₀ + (projectFinish d s) • L
      exact le_add_of_nonneg_right (nsmul_nonneg hL _)
    · intro j
      rw [← tickToTime_add]
      exact add_le_add_right
        (nsmul_le_nsmul_left hL (Finset.le_sup (f := fun j => s j + d j) (Finset.mem_univ j))) t₀
  · rintro t ⟨ht0, ht⟩
    rcases isEmpty_or_nonempty J with hJ | hJ
    · have := hJ
      rw [show projectFinish d s = 0 from by simp [projectFinish, Finset.univ_eq_empty]]
      simpa [tickToTime] using ht0
    · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup Finset.univ
        (Finset.univ_nonempty_iff.mpr hJ) (fun j => s j + d j)
      have hj' : projectFinish d s = s j + d j := hj
      rw [hj', tickToTime_add]
      exact ht j

end Cslib.Scheduling.ProjectNetwork
