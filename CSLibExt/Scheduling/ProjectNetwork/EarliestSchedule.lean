/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Scheduling.ProjectNetwork.JobSplitting
public import Mathlib.Order.Bounds.Defs

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Earliest job schedule and least project finish from the earliest event dates

A job table has jobs `J`, durations `d : J → ℕ` in ticks (zero allowed: a milestone) and a
precedence digraph `G : Digraph J`; its split network (`SplitEvent`, `SplitArc`) is the
activity-on-arc network of `CSLibExt.Scheduling.ProjectNetwork.JobSplitting`. Earliest event
dates are event times `τ` that are a feasible schedule of the split network and are attained:
every event `v` has a walk from the source of duration exactly `τ v`. For a finite acyclic table
`exists_isFeasibleSchedule_eq_sum`, with `finite_splitArc`, `eq_nil_of_isArcWalk_split_self` and
`exists_isArcWalk_source_sink`, provides them, and they put the source at tick `0`.

The earliest job schedule is `fun j => τ (.input j)`. This module proves that each job's output
event is its start plus its duration; that this schedule is precedence-feasible and is the least
precedence-feasible schedule in the pointwise order; that for a finite acyclic table its project
finish is the earliest date of the sink; and that its project finish is the least project finish
of any precedence-feasible schedule. No earliest-date recurrence or longest-path algorithm is
stated; resources are unlimited and there is no calendar, lag or real-valued duration.

Reference: J. E. Kelley Jr. and M. R. Walker, Critical-path planning and scheduling,
*Proceedings of the Eastern Joint Computer Conference*, 1959, pp. 160-173.
-/

namespace Cslib.Scheduling.ProjectNetwork

open MathlibExt.Combinatorics.Graph.ArcNetwork

/-- Earliest finishes: if `τ` is a feasible event schedule of the split network and every event
`v` has a walk from the source of duration exactly `τ v` (the earliest event dates), then the
output event of every job `j` occurs at its input event plus its duration,
`τ (.output j) = τ (.input j) + d j`. So the finish of job `j` under the earliest job schedule
`fun j => τ (.input j)` is the earliest date of its output event. No finiteness or acyclicity is
assumed. -/
theorem output_eq_input_add {J : Type*} {G : Digraph J} {d : J → ℕ}
    {τ : SplitEvent J → ℕ}
    (hτ : IsFeasibleSchedule (splitTail G) (splitHead G) (splitDuration G d) τ)
    (hwalk : ∀ v, ∃ l, IsArcWalk (splitTail G) (splitHead G) .source v l ∧
      (l.map (splitDuration G d)).sum = τ v)
    (j : J) : τ (.output j) = τ (.input j) + d j := by
  classical
  apply le_antisymm
  · set σ : SplitEvent J → ℕ := Function.update τ (.output j) (τ (.input j) + d j) with hσ
    have hsrc : σ .source = τ .source :=
      Function.update_of_ne (by simp : SplitEvent.source ≠ SplitEvent.output j) _ _
    have hsnk : σ .sink = τ .sink :=
      Function.update_of_ne (by simp : SplitEvent.sink ≠ SplitEvent.output j) _ _
    have hout : σ (.output j) = τ (.input j) + d j := Function.update_self _ _ _
    have hin : ∀ k, σ (.input k) = τ (.input k) :=
      fun k => Function.update_of_ne (by simp : SplitEvent.input k ≠ SplitEvent.output j) _ _
    have hjob : τ (.input j) + d j ≤ τ (.output j) := hτ (SplitArc.job j)
    have hσfeas : IsFeasibleSchedule (splitTail G) (splitHead G) (splitDuration G d) σ := by
      intro e
      cases e with
      | job j' =>
        show σ (.input j') + d j' ≤ σ (.output j')
        by_cases hj : j' = j
        · subst hj
          rw [hin, hout]
        · have hout' : σ (.output j') = τ (.output j') :=
            Function.update_of_ne (by simp [hj] : SplitEvent.output j' ≠ SplitEvent.output j) _ _
          rw [hin, hout']
          exact hτ (SplitArc.job j')
      | precedence i k h =>
        show σ (.output i) + 0 ≤ σ (.input k)
        by_cases hi : i = j
        · subst hi
          rw [hout, hin]
          have hprec : τ (.output i) + 0 ≤ τ (.input k) :=
            hτ (SplitArc.precedence _ _ h)
          omega
        · have houti : σ (.output i) = τ (.output i) :=
            Function.update_of_ne (by simp [hi] : SplitEvent.output i ≠ SplitEvent.output j) _ _
          rw [houti, hin]
          exact hτ (SplitArc.precedence _ _ h)
      | fromSource k h =>
        show σ .source + 0 ≤ σ (.input k)
        rw [hsrc, hin]
        exact hτ (SplitArc.fromSource _ h)
      | toSink k h =>
        show σ (.output k) + 0 ≤ σ .sink
        by_cases hk : k = j
        · subst hk
          rw [hout, hsnk]
          have hsnk' : τ (.output k) + 0 ≤ τ .sink := hτ (SplitArc.toSink _ h)
          omega
        · have houtk : σ (.output k) = τ (.output k) :=
            Function.update_of_ne (by simp [hk] : SplitEvent.output k ≠ SplitEvent.output j) _ _
          rw [houtk, hsnk]
          exact hτ (SplitArc.toSink _ h)
      | sourceSink =>
        show σ .source + 0 ≤ σ .sink
        rw [hsrc, hsnk]
        exact hτ SplitArc.sourceSink
    obtain ⟨m, hwm, hsm⟩ := hwalk (.output j)
    have hb := IsFeasibleSchedule.add_sum_map_le hσfeas hwm
    rw [hsrc, hout, hsm] at hb
    omega
  · exact hτ (SplitArc.job j)

private theorem input_le_of_feasible {J : Type*} {G : Digraph J} {d : J → ℕ}
    {τ : SplitEvent J → ℕ}
    (hwalk : ∀ v, ∃ l, IsArcWalk (splitTail G) (splitHead G) .source v l ∧
      (l.map (splitDuration G d)).sum = τ v)
    {s : J → ℕ} (hs : IsPrecedenceFeasible G d s) (j : J) :
    τ (.input j) ≤ s j := by
  suffices h : ∀ (o : SplitEvent J) (l : List (SplitArc G)),
      IsArcWalk (splitTail G) (splitHead G) o (.input j) l →
      (match o with
        | .source => (0 : ℕ)
        | .input k => s k
        | .output k => s k + d k
        | .sink => 0) + (l.map (splitDuration G d)).sum ≤ s j by
    obtain ⟨l, hwl, hsl⟩ := hwalk (.input j)
    have h1 := h .source l hwl
    dsimp only at h1
    omega
  intro o l
  induction l generalizing o with
  | nil =>
    intro hw
    obtain ⟨hempty, _, _, _⟩ := hw
    have ho : o = .input j := hempty rfl
    subst ho
    simp
  | cons e l' ih =>
    intro hw
    obtain ⟨_, hhead, hchain, hlast⟩ := hw
    have htail : splitTail G e = o := hhead e rfl
    rw [List.isChain_cons] at hchain
    obtain ⟨hrel, hchain'⟩ := hchain
    have hw' : IsArcWalk (splitTail G) (splitHead G) (splitHead G e) (.input j) l' := by
      refine ⟨?_, ?_, hchain', ?_⟩
      · intro hnil
        subst hnil
        exact hlast e rfl
      · intro y hy
        exact (hrel y hy).symm
      · intro y hy
        cases l' with
        | nil => simp at hy
        | cons _b _l'' => exact hlast y hy
    have ih' := ih (splitHead G e) hw'
    cases e with
    | job k =>
      have ho : o = SplitEvent.input k := htail.symm
      subst ho
      have ih'' : s k + d k + (l'.map (splitDuration G d)).sum ≤ s j := ih'
      show s k + (d k + (l'.map (splitDuration G d)).sum) ≤ s j
      omega
    | precedence i k h =>
      have ho : o = SplitEvent.output i := htail.symm
      subst ho
      have ih'' : s k + (l'.map (splitDuration G d)).sum ≤ s j := ih'
      have hsk : s i + d i ≤ s k := hs h
      show s i + d i + (0 + (l'.map (splitDuration G d)).sum) ≤ s j
      omega
    | fromSource k _ =>
      have ho : o = SplitEvent.source := htail.symm
      subst ho
      have ih'' : s k + (l'.map (splitDuration G d)).sum ≤ s j := ih'
      show 0 + (0 + (l'.map (splitDuration G d)).sum) ≤ s j
      omega
    | toSink k _ =>
      exfalso
      cases l' with
      | nil =>
        have h1 := hw'.1 rfl
        simp [splitHead] at h1
      | cons b _l'' =>
        have h2 := hw'.2.1 b rfl
        cases b with
        | job _ => simp [splitTail, splitHead] at h2
        | precedence _ _ _ => simp [splitTail, splitHead] at h2
        | fromSource _ _ => simp [splitTail, splitHead] at h2
        | toSink _ _ => simp [splitTail, splitHead] at h2
        | sourceSink => simp [splitTail, splitHead] at h2
    | sourceSink =>
      have ho : o = SplitEvent.source := htail.symm
      subst ho
      have ih'' : 0 + (l'.map (splitDuration G d)).sum ≤ s j := ih'
      show 0 + (0 + (l'.map (splitDuration G d)).sum) ≤ s j
      omega

/-- Feasible earliest job schedule: under the earliest event dates `τ` of the split network
(`hτ`, `hwalk`), the start ticks `fun j => τ (.input j)` are the least precedence-feasible start
schedule. They satisfy every precedence constraint, and every precedence-feasible schedule `s`
starts each job `j` no earlier, `τ (.input j) ≤ s j` (the order on start schedules is
pointwise). No finiteness or acyclicity is assumed. -/
theorem isLeast_input {J : Type*} {G : Digraph J} {d : J → ℕ}
    {τ : SplitEvent J → ℕ}
    (hτ : IsFeasibleSchedule (splitTail G) (splitHead G) (splitDuration G d) τ)
    (hwalk : ∀ v, ∃ l, IsArcWalk (splitTail G) (splitHead G) .source v l ∧
      (l.map (splitDuration G d)).sum = τ v) :
    IsLeast {s : J → ℕ | IsPrecedenceFeasible G d s} fun j => τ (.input j) := by
  have _hsrc : τ .source = 0 := by
    obtain ⟨l, hwl, hsl⟩ := hwalk .source
    have hb := IsFeasibleSchedule.add_sum_map_le hτ hwl
    omega
  refine ⟨isPrecedenceFeasible_input hτ, ?_⟩
  rw [mem_lowerBounds]
  intro s hs
  rw [Pi.le_def]
  intro j
  exact input_le_of_feasible hwalk hs j

/-- Project finish transport: for a finite acyclic table, the project finish of the earliest
job schedule `fun j => τ (.input j)` is the earliest date of the sink event of the split
network. Acyclicity is needed: a cyclic part of the table with zero-duration cycles can have
earliest event dates whose job finishes are not bounded by the sink. -/
theorem projectFinish_input_eq_sink {J : Type*} [Fintype J] {G : Digraph J} {d : J → ℕ}
    (hG : G.IsAcyclic) {τ : SplitEvent J → ℕ}
    (hτ : IsFeasibleSchedule (splitTail G) (splitHead G) (splitDuration G d) τ)
    (hwalk : ∀ v, ∃ l, IsArcWalk (splitTail G) (splitHead G) .source v l ∧
      (l.map (splitDuration G d)).sum = τ v) :
    projectFinish d (fun j => τ (.input j)) = τ .sink := by
  apply le_antisymm
  · exact projectFinish_input_le_sink hG hτ
  · obtain ⟨m, hwm, hsm⟩ := hwalk .sink
    have hfeas : IsFeasibleSchedule (splitTail G) (splitHead G) (splitDuration G d)
        (embedSchedule d fun j => τ (.input j)) := isFeasibleSchedule_embedSchedule (isPrecedenceFeasible_input hτ)
    have hb := IsFeasibleSchedule.add_sum_map_le hfeas hwm
    have hb' : (0 : ℕ) + (m.map (splitDuration G d)).sum ≤
        projectFinish d (fun j => τ (.input j)) := hb
    omega

/-- Minimal project finish: under the earliest event dates `τ` of the split network (`hτ`,
`hwalk`), the project finish of the earliest job schedule `fun j => τ (.input j)` is the least
project finish of any precedence-feasible start schedule: it is the project finish of a
precedence-feasible schedule, and no precedence-feasible schedule finishes earlier. No
acyclicity is assumed; `Fintype J` is needed for the project finish. -/
theorem isLeast_projectFinish_input {J : Type*} [Fintype J] {G : Digraph J} {d : J → ℕ}
    {τ : SplitEvent J → ℕ}
    (hτ : IsFeasibleSchedule (splitTail G) (splitHead G) (splitDuration G d) τ)
    (hwalk : ∀ v, ∃ l, IsArcWalk (splitTail G) (splitHead G) .source v l ∧
      (l.map (splitDuration G d)).sum = τ v) :
    IsLeast (projectFinish d '' {s : J → ℕ | IsPrecedenceFeasible G d s})
      (projectFinish d fun j => τ (.input j)) := by
  have _hsrc : τ .source = 0 := by
    obtain ⟨l, hwl, hsl⟩ := hwalk .source
    have hb := IsFeasibleSchedule.add_sum_map_le hτ hwl
    omega
  refine ⟨⟨fun j => τ (.input j), isPrecedenceFeasible_input hτ, rfl⟩, ?_⟩
  rw [mem_lowerBounds]
  intro y hy
  rw [Set.mem_image] at hy
  obtain ⟨s, hs, rfl⟩ := hy
  apply Finset.sup_le
  intro j _
  have hle : τ (.input j) ≤ s j := input_le_of_feasible hwalk hs j
  have h1 : τ (.input j) + d j ≤ s j + d j := by omega
  have h2 : s j + d j ≤ Finset.univ.sup (fun j => s j + d j) :=
    Finset.le_sup (s := Finset.univ) (f := fun j => s j + d j) (b := j)
      (Finset.mem_univ j)
  have h3 : τ (.input j) + d j ≤ Finset.univ.sup (fun j => s j + d j) := le_trans h1 h2
  exact h3

end Cslib.Scheduling.ProjectNetwork
