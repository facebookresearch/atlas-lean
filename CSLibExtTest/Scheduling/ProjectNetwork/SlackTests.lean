/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Scheduling.ProjectNetwork.Slack
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Slack and total float checks

Concrete consumers of `CSLibExt.Scheduling.ProjectNetwork.Slack`: the critical arcs of the
three-event network of `slack_eq_zero_totalFloat_eq_one` and its project length as the least
finish time of a schedule with no event before the start, the one-event network with no
activity, an activity of negative duration, a negative duration for which that least finish time
differs from the project length, and a network with an event that reaches no sink, on which the
slack of that event is negative, so the coverage hypothesis of `critical_path_slack` is needed.
Elaboration checks, not results.
-/

namespace CSLibExtTest.Scheduling.ProjectNetwork.Slack

open Cslib.Scheduling.ProjectNetwork MathlibExt.Combinatorics.Graph.ArcNetwork

/-! ### The three-event network: `s → t`, `s → 1`, `1 → t`, each of duration `1` -/

/-- Tails of the arcs `s → t`, `s → 1` and `1 → t`, with `s = 0` and `t = 2`. -/
abbrev tail₃ : Fin 3 → Fin 3 := ![0, 0, 1]

/-- Heads of the arcs `s → t`, `s → 1` and `1 → t`. -/
abbrev head₃ : Fin 3 → Fin 3 := ![2, 1, 2]

/-- Unit durations. -/
abbrev d₃ : Fin 3 → ℤ := fun _ => 1

theorem walk₃ {u v : Fin 3} {l : List (Fin 3)} (hl : IsArcWalk tail₃ head₃ u v l) :
    ((u : ℕ) : ℤ) + l.length ≤ ((v : ℕ) : ℤ) := by
  have hτ : ∀ e, ((tail₃ e : ℕ) : ℤ) + d₃ e ≤ ((head₃ e : ℕ) : ℤ) := by
    intro e
    fin_cases e <;> decide
  simpa using add_sum_map_le_of_forall_add_le (τ := fun v : Fin 3 => ((v : ℕ) : ℤ)) hτ hl

theorem acyclic₃ : ∀ v (l : List (Fin 3)), IsArcWalk tail₃ head₃ v v l → l = [] := by
  intro v l hl
  have := walk₃ hl
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem cover₃ : ∀ v : Fin 3,
    (∃ l, IsArcWalk tail₃ head₃ 0 v l) ∧ ∃ l, IsArcWalk tail₃ head₃ v 2 l := by
  intro v
  fin_cases v
  · exact ⟨⟨[], walk_nil⟩, [0], walk_singleton rfl rfl⟩
  · exact ⟨⟨[1], walk_singleton rfl rfl⟩, [2], walk_singleton rfl rfl⟩
  · exact ⟨⟨[0], walk_singleton rfl rfl⟩, [], walk_nil⟩

/-- The project length is `2`: the least project duration is at most that of the event schedule
`0, 1, 2`, and the walk `s → 1 → t` lasts `2`. -/
theorem longestDuration₃ : longestDuration tail₃ head₃ d₃ 0 2 = 2 := by
  obtain ⟨hgreat, hleast, -⟩ := critical_path_slack (d := d₃) acyclic₃ cover₃
  refine le_antisymm ?_ ((hgreat 0 2 ⟨_, walk_singleton (a := 0) rfl rfl⟩).2 ⟨[1, 2], ?_, rfl⟩)
  · refine hleast.2 ⟨fun v => ((v : ℕ) : ℤ), fun e => ?_, rfl⟩
    fin_cases e <;> decide
  · exact walk_cons_mk rfl (walk_singleton rfl rfl)

/-- The arcs `s → 1` and `1 → t` of the longest walk have total float `0`. -/
example : totalFloat tail₃ head₃ d₃ 0 2 1 = 0 ∧ totalFloat tail₃ head₃ d₃ 0 2 2 = 0 := by
  obtain ⟨-, -, -, -, -, -, hzero⟩ := critical_path_slack (d := d₃) acyclic₃ cover₃
  have hwalk : IsArcWalk tail₃ head₃ 0 2 [1, 2] := walk_cons_mk rfl (walk_singleton rfl rfl)
  exact ⟨(hzero 1).2 ⟨_, hwalk, by rw [longestDuration₃]; rfl, by simp⟩,
    (hzero 2).2 ⟨_, hwalk, by rw [longestDuration₃]; rfl, by simp⟩⟩

/-- The arc `s → t` lies on no walk of the project length. -/
example : ¬ ∃ l, IsArcWalk tail₃ head₃ 0 2 l ∧
    (l.map d₃).sum = longestDuration tail₃ head₃ d₃ 0 2 ∧ (0 : Fin 3) ∈ l := by
  obtain ⟨-, -, -, -, -, -, hzero⟩ := critical_path_slack (d := d₃) acyclic₃ cover₃
  rw [← hzero]
  norm_num [totalFloat, latestStart, earliestStart, longestDuration_self acyclic₃, longestDuration₃]

/-- Its event `1` has slack `0`. -/
example : latestStart tail₃ head₃ d₃ 0 2 1 - earliestStart tail₃ head₃ d₃ 0 1 = 0 := by
  obtain ⟨-, -, -, -, hzero, -⟩ := critical_path_slack (d := d₃) acyclic₃ cover₃
  exact (hzero 1).2 ⟨[1], [2], walk_singleton rfl rfl, walk_singleton rfl rfl, by
    rw [longestDuration₃]; rfl⟩

/-- With nonnegative durations the project length `2` is also the least finish time of an event
schedule that starts at time `0` and puts no event before it. -/
example : IsLeast {x | ∃ τ : Fin 3 → ℤ, (∀ e, τ (tail₃ e) + d₃ e ≤ τ (head₃ e)) ∧ τ 0 = 0 ∧
    (∀ v, 0 ≤ τ v) ∧ τ 2 = x} 2 := by
  obtain ⟨-, -, hnonneg, -⟩ := critical_path_slack (d := d₃) acyclic₃ cover₃
  rw [← longestDuration₃]
  exact (hnonneg fun _ => zero_le_one).2

/-- The real form of the example as stated. -/
example : totalFloat (![0, 0, 1] : Fin 3 → Fin 3) ![2, 1, 2] (fun _ : Fin 3 => (1 : ℝ)) 0 2 0 =
    1 :=
  slack_eq_zero_totalFloat_eq_one.2.2

/-! ### One event and no activity -/

/-- With a single event, which is both source and sink, and no activity, the project length is
`0` and the event has slack `0`. -/
example (d : Empty → ℤ) :
    longestDuration (Empty.elim : Empty → Unit) Empty.elim d () () = 0 ∧
      latestStart (Empty.elim : Empty → Unit) Empty.elim d () () () -
        earliestStart (Empty.elim : Empty → Unit) Empty.elim d () () = 0 := by
  have hacyc : ∀ v (l : List Empty), IsArcWalk (Empty.elim : Empty → Unit) Empty.elim v v l →
      l = [] := fun _ l _ => match l with | [] => rfl
  have hcover : ∀ v : Unit, (∃ l, IsArcWalk (Empty.elim : Empty → Unit) Empty.elim () v l) ∧
      ∃ l, IsArcWalk (Empty.elim : Empty → Unit) Empty.elim v () l :=
    fun _ => ⟨⟨[], walk_nil⟩, [], walk_nil⟩
  obtain ⟨-, -, -, -, hzero, -⟩ := critical_path_slack (d := d) hacyc hcover
  refine ⟨longestDuration_self hacyc (), (hzero ()).2 ⟨[], [], walk_nil, walk_nil, ?_⟩⟩
  rw [longestDuration_self hacyc]
  rfl

/-! ### A negative duration -/

/-- No sign condition: a single activity `s → t` of duration `-1` has total float `0`, and the
least project duration is `-1`. -/
example : totalFloat (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => (-1 : ℤ)) 0 1 () = 0 ∧
    IsLeast {x | ∃ τ : Fin 2 → ℤ, (∀ _ : Unit, τ 0 + (-1) ≤ τ 1) ∧ τ 1 - τ 0 = x} (-1) := by
  have hwalk : ∀ {u v : Fin 2} {l : List Unit},
      IsArcWalk (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) u v l → ((u : ℕ) : ℤ) + l.length ≤ v :=
    fun hl => by
      simpa using add_sum_map_le_of_forall_add_le (τ := fun v : Fin 2 => ((v : ℕ) : ℤ))
        (d := fun _ : Unit => (1 : ℤ)) (fun _ => le_rfl) hl
  have hacyc : ∀ v (l : List Unit), IsArcWalk (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) v v l →
      l = [] := fun _ _ hl => List.eq_nil_of_length_eq_zero (by have := hwalk hl; omega)
  have hcover : ∀ v : Fin 2, (∃ l, IsArcWalk (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) 0 v l) ∧
      ∃ l, IsArcWalk (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) v 1 l := by
    intro v
    fin_cases v
    · exact ⟨⟨[], walk_nil⟩, [()], walk_singleton rfl rfl⟩
    · exact ⟨⟨[()], walk_singleton rfl rfl⟩, [], walk_nil⟩
  obtain ⟨hgreat, hleast, -, -, -, -, hzero⟩ :=
    critical_path_slack (d := fun _ : Unit => (-1 : ℤ)) hacyc hcover
  have hL : longestDuration (fun _ : Unit => (0 : Fin 2)) (fun _ => 1) (fun _ => (-1 : ℤ)) 0 1 =
      -1 := by
    refine le_antisymm ?_ ((hgreat 0 1 ⟨_, walk_singleton (a := ()) rfl rfl⟩).2
      ⟨[()], walk_singleton rfl rfl, rfl⟩)
    exact hleast.2 ⟨fun v => -((v : ℕ) : ℤ), fun _ => by decide, by decide⟩
  refine ⟨(hzero ()).2 ⟨[()], walk_singleton rfl rfl, by rw [hL]; rfl, by simp⟩, ?_⟩
  rwa [hL] at hleast

/-- Tails of the arcs `s → 1` and `1 → t`, with `s = 0` and `t = 2`. -/
abbrev tailNeg : Fin 2 → Fin 3 := ![0, 1]

/-- Heads of the arcs `s → 1` and `1 → t`. -/
abbrev headNeg : Fin 2 → Fin 3 := ![1, 2]

/-- Durations `-1` and `1`. -/
abbrev dNeg : Fin 2 → ℤ := ![-1, 1]

/-- With a negative duration the event-schedule clause and the linear program with no event
before the start differ: for the arcs `s → 1` of duration `-1` and `1 → t` of duration `1`, the
project length is `0`, attained by the event times `0, -1, 0`, but every event schedule with
`τ s = 0` and no negative event time finishes at time `1` or later. -/
example : longestDuration tailNeg headNeg dNeg 0 2 = 0 ∧
    IsLeast {x | ∃ τ : Fin 3 → ℤ, (∀ e, τ (tailNeg e) + dNeg e ≤ τ (headNeg e)) ∧ τ 0 = 0 ∧
      (∀ v, 0 ≤ τ v) ∧ τ 2 = x} 1 := by
  have hacyc : ∀ v (l : List (Fin 2)), IsArcWalk tailNeg headNeg v v l → l = [] := by
    intro v l hl
    have h : ∀ e, ((tailNeg e : ℕ) : ℤ) + 1 ≤ ((headNeg e : ℕ) : ℤ) := by
      intro e
      fin_cases e <;> decide
    have h' : ((v : ℕ) : ℤ) + l.length ≤ ((v : ℕ) : ℤ) := by
      simpa using add_sum_map_le_of_forall_add_le (τ := fun v : Fin 3 => ((v : ℕ) : ℤ))
        (d := fun _ : Fin 2 => (1 : ℤ)) h hl
    exact List.eq_nil_of_length_eq_zero (by omega)
  have h01 : IsArcWalk tailNeg headNeg 0 2 [0, 1] := walk_cons_mk rfl (walk_singleton rfl rfl)
  have hcover : ∀ v : Fin 3, (∃ l, IsArcWalk tailNeg headNeg 0 v l) ∧
      ∃ l, IsArcWalk tailNeg headNeg v 2 l := by
    intro v
    fin_cases v
    · exact ⟨⟨[], walk_nil⟩, _, h01⟩
    · exact ⟨⟨[0], walk_singleton rfl rfl⟩, [1], walk_singleton rfl rfl⟩
    · exact ⟨⟨_, h01⟩, [], walk_nil⟩
  obtain ⟨hgreat, hleast, -⟩ := critical_path_slack (d := dNeg) hacyc hcover
  refine ⟨le_antisymm ?_ ((hgreat 0 2 ⟨_, h01⟩).2 ⟨_, h01, rfl⟩), ⟨![0, 0, 1], ?_, rfl, ?_, rfl⟩,
    ?_⟩
  · refine hleast.2 ⟨![0, -1, 0], fun e => ?_, rfl⟩
    fin_cases e <;> decide
  · intro e
    fin_cases e <;> decide
  · intro v
    fin_cases v <;> decide
  · rintro _ ⟨τ, hτ, -, hnn, rfl⟩
    -- `τ 1 + 1 ≤ τ 2` and `0 ≤ τ 1`.
    have h1 : τ 1 + 1 ≤ τ 2 := by simpa using hτ 1
    have h2 := hnn 1
    show (1 : ℤ) ≤ τ 2
    omega

/-! ### Coverage is needed -/

/-- Tails of the arcs `s → 1` and `s → t`, with `s = 0` and `t = 2`; the event `1` reaches no
sink. -/
abbrev tailOff : Fin 2 → Fin 3 := ![0, 0]

/-- Heads of the arcs `s → 1` and `s → t`. -/
abbrev headOff : Fin 2 → Fin 3 := ![1, 2]

/-- Durations `5` and `1`. -/
abbrev dOff : Fin 2 → ℤ := ![5, 1]

/-- Without the coverage hypothesis the slack can be negative: in the network `s → 1` of
duration `5` and `s → t` of duration `1`, the event `1`, which reaches no sink, has earliest start
`5`, and its latest start takes the junk value `0` for a longest walk from `1` to `t`, so its slack
is `1 - 5 = -4`. -/
example : latestStart tailOff headOff dOff 0 2 1 - earliestStart tailOff headOff dOff 0 1 = -4 := by
  have hτ : ∀ e, ![(0 : ℤ), 5, 1] (tailOff e) + dOff e ≤ ![(0 : ℤ), 5, 1] (headOff e) := by
    intro e
    fin_cases e <;> decide
  have hacyc : ∀ v (l : List (Fin 2)), IsArcWalk tailOff headOff v v l → l = [] := by
    intro v l hl
    have hlen : ∀ {u w : Fin 3} {l : List (Fin 2)}, IsArcWalk tailOff headOff u w l →
        ((u : ℕ) : ℤ) + l.length ≤ ((w : ℕ) : ℤ) := fun hl => by
      have h : ∀ e, ((tailOff e : ℕ) : ℤ) + 1 ≤ ((headOff e : ℕ) : ℤ) := by
        intro e
        fin_cases e <;> decide
      simpa using add_sum_map_le_of_forall_add_le (τ := fun v : Fin 3 => ((v : ℕ) : ℤ))
        (d := fun _ : Fin 2 => (1 : ℤ)) h hl
    exact List.eq_nil_of_length_eq_zero (by have := hlen hl; omega)
  -- No walk leads from the event `1` to the sink.
  have hnone : ∀ l, ¬ IsArcWalk tailOff headOff 1 2 l := by
    rintro (_ | ⟨a, l⟩) hl
    · exact absurd (hl.1 rfl) (by decide)
    · have := (walk_cons_pair hl).1
      fin_cases a <;> simp at this
  have hjunk : longestDuration tailOff headOff dOff 1 2 = 0 := by
    rw [longestDuration, dite_eq_right]
    rintro ⟨x, ⟨l, hl, -⟩, -⟩
    exact hnone l hl
  have h01 : longestDuration tailOff headOff dOff 0 1 = 5 := by
    have hw : IsArcWalk tailOff headOff 0 1 [0] := walk_singleton rfl rfl
    refine le_antisymm ?_ (by simpa using sum_map_le_longestDuration (d := dOff) hacyc hw)
    obtain ⟨l, hl, hsum⟩ := exists_sum_map_eq_longestDuration (d := dOff) hacyc ⟨_, hw⟩
    rw [← hsum]
    simpa using add_sum_map_le_of_forall_add_le hτ hl
  have h02 : longestDuration tailOff headOff dOff 0 2 = 1 := by
    have hw : IsArcWalk tailOff headOff 0 2 [1] := walk_singleton rfl rfl
    refine le_antisymm ?_ (by simpa using sum_map_le_longestDuration (d := dOff) hacyc hw)
    obtain ⟨l, hl, hsum⟩ := exists_sum_map_eq_longestDuration (d := dOff) hacyc ⟨_, hw⟩
    rw [← hsum]
    simpa using add_sum_map_le_of_forall_add_le hτ hl
  simp only [latestStart, earliestStart, hjunk, h01, h02]
  decide

end CSLibExtTest.Scheduling.ProjectNetwork.Slack
