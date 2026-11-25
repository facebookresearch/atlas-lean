/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Scheduling.ProjectNetwork.EarliestSchedule

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Critical-path job witness

A job table has jobs `J`, durations `d : J → ℕ` in ticks (zero allowed: a milestone) and a
precedence digraph `G : Digraph J`; its split network (`SplitEvent`, `SplitArc`) is the
activity-on-arc network of `CSLibExt.Scheduling.ProjectNetwork.JobSplitting`. For a finite acyclic
table, earliest event dates `τ` are a feasible schedule of the split network in which every event
`v` has a walk from the source of duration exactly `τ v`; the earliest project finish is
`projectFinish d (fun j => τ (.input j))`, which equals the earliest sink date `τ .sink`
(`projectFinish_input_eq_sink`).

A critical-path certificate is a source-to-sink walk `l` of the split network whose duration is the
earliest sink date, `(l.map (splitDuration G d)).sum = τ .sink`: by the critical-path lower bound
every source-to-sink walk lasts at most `τ .sink`, so `l` has maximum duration, and the walk that
the earliest dates provide at the sink is one. Its job sequence `l.filterMap SplitArc.job?` drops
exactly the zero-lag arcs and keeps every traversed duration arc in traversal order, a milestone's
included. This module proves that the job sequence of every certificate is a directed path of `G`
that runs from a start job to a finish job when nonempty, that its total job duration is the
earliest project finish, and that it is empty exactly when the certificate is the declared
source-to-sink arc; and that the empty job list is the job sequence of a certificate exactly when
every job has duration `0`. No longest-path algorithm, earliest-date recurrence, backward pass,
float, calendar, lag or resource limit is stated.

Reference: J. E. Kelley Jr. and M. R. Walker, Critical-path planning and scheduling,
*Proceedings of the Eastern Joint Computer Conference*, 1959, pp. 160-173.
-/

namespace Cslib.Scheduling.ProjectNetwork

open MathlibExt.Combinatorics.Graph.ArcNetwork

/-- Critical-path job witness: for a finite acyclic table with earliest event dates `τ` (`hτ`,
`hwalk`), let `l` be a critical-path certificate, a source-to-sink walk of the split network
whose duration is the earliest sink date `τ .sink`. Its job sequence
`l.filterMap SplitArc.job?`, which drops the zero-lag arcs and keeps each traversed duration arc
in traversal order, is a directed path of the precedence digraph (a precedence chain with no
repeated job); if nonempty, it begins at a start job and ends at a finish job; its total job
duration is the earliest project finish `projectFinish d (fun j => τ (.input j))`; and it is
empty exactly when `l` is the declared source-to-sink arc. Every certificate qualifies, so
either of two tied critical paths gives a witness. -/
theorem mem_paths_filterMap_job?_of_sum_eq_sink {J : Type*} [Fintype J] {G : Digraph J}
    {d : J → ℕ}
    (hG : G.IsAcyclic) {τ : SplitEvent J → ℕ}
    (hτ : IsFeasibleSchedule (splitTail G) (splitHead G) (splitDuration G d) τ)
    (hwalk : ∀ v, ∃ l, IsArcWalk (splitTail G) (splitHead G) .source v l ∧
      (l.map (splitDuration G d)).sum = τ v)
    {l : List (SplitArc G)} (hl : IsArcWalk (splitTail G) (splitHead G) .source .sink l)
    (hdur : (l.map (splitDuration G d)).sum = τ .sink) :
    l.filterMap SplitArc.job? ∈ G.paths ∧
      (∀ j ∈ (l.filterMap SplitArc.job?).head?, ∀ i, ¬ G.Adj i j) ∧
      (∀ j ∈ (l.filterMap SplitArc.job?).getLast?, ∀ k, ¬ G.Adj j k) ∧
      ((l.filterMap SplitArc.job?).map d).sum = projectFinish d (fun j => τ (.input j)) ∧
      (l.filterMap SplitArc.job? = [] ↔ l = [.sourceSink]) := by
  obtain ⟨hchain, hhead, hlast, hempty⟩ := isChain_filterMap_job?_of_isArcWalk hl
  have hnodup' : (l.filterMap SplitArc.job?).Nodup := hG.nodup_of_isChain hchain
  have hmem : l.filterMap SplitArc.job? ∈ G.paths := ⟨hchain, hnodup'⟩
  have hdur' : ((l.filterMap SplitArc.job?).map d).sum =
      projectFinish d (fun j => τ (.input j)) := by
    rw [← sum_map_splitDuration d l, hdur, ← projectFinish_input_eq_sink hG hτ hwalk]
  exact ⟨hmem, hhead, hlast, hdur', hempty⟩

/-- Empty witness at duration zero: for a finite acyclic table with earliest event dates `τ`
(`hτ`, `hwalk`), the empty job list is the job sequence of a critical-path certificate (a
source-to-sink walk of the split network whose duration is the earliest sink date `τ .sink`)
exactly when every job has duration `0`, that is, exactly when the longest precedence chain has
duration `0`. That certificate is then the declared source-to-sink arc
(`mem_paths_filterMap_job?_of_sum_eq_sink`), and for an empty job type the condition holds
vacuously. Acyclicity is needed: a positive-duration job followed only by a cycle of
zero-duration jobs never reaches the sink, and the declared arc then attains the sink date `0`.
So is finiteness: an infinite chain of unit-duration jobs has no finish job. -/
theorem exists_isArcWalk_sum_eq_sink_filterMap_job?_eq_nil_iff {J : Type*} [Finite J]
    {G : Digraph J} {d : J → ℕ}
    (hG : G.IsAcyclic) {τ : SplitEvent J → ℕ}
    (hτ : IsFeasibleSchedule (splitTail G) (splitHead G) (splitDuration G d) τ)
    (hwalk : ∀ v, ∃ l, IsArcWalk (splitTail G) (splitHead G) .source v l ∧
      (l.map (splitDuration G d)).sum = τ v) :
    (∃ l, IsArcWalk (splitTail G) (splitHead G) .source .sink l ∧
        (l.map (splitDuration G d)).sum = τ .sink ∧ l.filterMap SplitArc.job? = []) ↔
      ∀ j, d j = 0 := by
  constructor
  · rintro ⟨l, _, hdur, hnil⟩
    have hsuml := sum_map_splitDuration d l
    rw [hnil] at hsuml
    simp at hsuml
    have hsink : τ .sink = 0 := by rw [← hdur, hsuml]
    intro j
    obtain ⟨_, ⟨l2, h2⟩⟩ := exists_isArcWalk_source_sink hG (.output j)
    have hle := IsFeasibleSchedule.add_sum_map_le hτ h2
    rw [hsink] at hle
    have hout : τ (.output j) = 0 := by omega
    have hfeas : τ (.input j) + d j ≤ τ (.output j) := hτ (.job j)
    omega
  · intro hall
    have hall0 : ∀ js : List J, (js.map d).sum = 0 := by
      intro js
      induction js with
      | nil => rfl
      | cons hd tl ih => simp [hall hd, ih]
    obtain ⟨lw, _, hdurw⟩ := hwalk (.sink)
    have hsumw := sum_map_splitDuration d lw
    have h0 : (lw.map (splitDuration G d)).sum = 0 := hsumw.trans (hall0 _)
    have hsink0 : τ .sink = 0 := hdurw.symm.trans h0
    have hwalkSS : IsArcWalk (splitTail G) (splitHead G) .source .sink [.sourceSink] := by
      unfold IsArcWalk
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp
      · intro e he
        simp at he
        subst he
        rfl
      · exact List.isChain_singleton _
      · intro e he
        simp at he
        subst he
        rfl
    have hsing : (([.sourceSink].map (splitDuration G d)).sum) = 0 := rfl
    have hdurSS : (([.sourceSink].map (splitDuration G d)).sum) = τ .sink := by
      rw [hsing, hsink0]
    have hnilSS : (([.sourceSink] : List (SplitArc G)).filterMap SplitArc.job?) = [] := rfl
    exact ⟨[.sourceSink], hwalkSS, hdurSS, hnilSS⟩

end Cslib.Scheduling.ProjectNetwork
