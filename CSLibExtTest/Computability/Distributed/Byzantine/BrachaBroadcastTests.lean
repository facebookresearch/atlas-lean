/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.Byzantine.BrachaBroadcast
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Prod

/-!
# Tests for Bracha's Byzantine reliable broadcast

* Fair executions exist: from any state, a scheduler that delivers pending messages of
  non-faulty parties, and stutters when there are none, runs a fair infinite execution when
  the values are finite. So the fairness hypothesis of `bracha_reliable_broadcast` is satisfiable.
* With a non-faulty leader, every non-faulty party delivers the input in that execution.
* The main theorem applies to four parties and one fault.
* A faulty leader may stay silent: the stuttering execution is then fair and nobody delivers.
  With a non-faulty leader the same execution is not fair.
* The bound `n > 3 f` cannot be dropped: with three parties and one fault, a faulty leader makes
  two non-faulty parties deliver different values.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.Byzantine.BrachaBroadcast.Tests

open Finset

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]

section Scheduler

variable (f : ℕ) (leader : P) (F : Finset P)

/-- One step of the scheduler: deliver some pending message that a non-faulty party has sent,
or stutter if there is none. -/
noncomputable def schedStep (s : BrachaState P V) :
    Option (P × P × BrachaKind × V) × BrachaState P V := by
  classical
  exact if h : ∃ x t, (brachaLTS f leader F).Tr s (some x) t ∧ x ∈ s.sent then
    (some h.choose, h.choose_spec.choose) else (none, s)

lemma schedStep_tr (s : BrachaState P V) :
    (brachaLTS f leader F).Tr s (schedStep f leader F s).1 (schedStep f leader F s).2 := by
  unfold schedStep
  split_ifs with h
  · exact h.choose_spec.choose_spec.1
  · rfl

lemma schedStep_of_stuck {s : BrachaState P V}
    (h : ¬∃ x t, (brachaLTS f leader F).Tr s (some x) t ∧ x ∈ s.sent) :
    schedStep f leader F s = (none, s) := by
  unfold schedStep
  rw [dite_eq_right h]

/-- The states of the scheduled execution from `s`. -/
noncomputable def schedStates (s : BrachaState P V) : ℕ → BrachaState P V
  | 0 => s
  | k + 1 => (schedStep f leader F (schedStates s k)).2

/-- The labels of the scheduled execution from `s`. -/
noncomputable def schedLabels (s : BrachaState P V) (k : ℕ) : Option (P × P × BrachaKind × V) :=
  (schedStep f leader F (schedStates f leader F s k)).1

lemma schedStates_exec (s : BrachaState P V) :
    (brachaLTS f leader F).OmegaExecution (schedStates f leader F s : ωSequence (BrachaState P V))
      (schedLabels f leader F s : ωSequence (Option (P × P × BrachaKind × V))) :=
  fun k => schedStep_tr f leader F (schedStates f leader F s k)

variable {f leader F}

lemma sent_subset_of_tr {s t : BrachaState P V} {a : Option (P × P × BrachaKind × V)}
    (h : (brachaLTS f leader F).Tr s a t) : s.sent ⊆ t.sent := by
  rcases a with _ | x
  · cases h
    exact subset_rfl
  · obtain ⟨-, -, -, rfl⟩ := h
    exact Set.subset_union_left

/-- The total number of messages received, summed over the parties. -/
noncomputable def received (s : BrachaState P V) : ℕ := ∑ i, #(s.rcvd i)

lemma received_lt_of_tr {s t : BrachaState P V} {x : P × P × BrachaKind × V}
    (h : (brachaLTS f leader F).Tr s (some x) t) : received s < received t := by
  obtain ⟨q, i, k, v⟩ := x
  obtain ⟨-, -, hnew, rfl⟩ := h
  refine sum_lt_sum (fun j _ => ?_) ⟨i, mem_univ i, ?_⟩
  · by_cases hj : j = i
    · subst hj
      simpa using card_le_card (subset_insert (q, k, v) (s.rcvd j))
    · simp [hj]
  · simp [card_insert_of_notMem hnew]

omit [DecidableEq P] [DecidableEq V] in
lemma received_le [Fintype V] (s : BrachaState P V) :
    received s ≤ Fintype.card P * Fintype.card (P × BrachaKind × V) := by
  calc received s ≤ ∑ _i : P, Fintype.card (P × BrachaKind × V) :=
        sum_le_sum fun i _ => card_le_univ _
    _ = Fintype.card P * Fintype.card (P × BrachaKind × V) := by
        rw [sum_const, card_univ]
        rfl

/-- With finitely many values, the scheduler eventually has nothing left to deliver. -/
lemma exists_stuck [Fintype V] (s : BrachaState P V) : ∃ K,
    ¬∃ x t, (brachaLTS f leader F).Tr (schedStates f leader F s K) (some x) t ∧
      x ∈ (schedStates f leader F s K).sent := by
  by_contra hcon
  push Not at hcon
  have hgrow : ∀ k, k ≤ received (schedStates f leader F s k) := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hk := hcon k
      have hstep : schedStep f leader F (schedStates f leader F s k) =
          (some hk.choose, hk.choose_spec.choose) := by
        unfold schedStep
        rw [dite_eq_left hk]
      have htr := hk.choose_spec.choose_spec.1
      have hlt := received_lt_of_tr htr
      change k + 1 ≤ received (schedStep f leader F (schedStates f leader F s k)).2
      rw [hstep]
      dsimp only
      omega
  have := hgrow (Fintype.card P * Fintype.card (P × BrachaKind × V) + 1)
  have := received_le
    (schedStates f leader F s (Fintype.card P * Fintype.card (P × BrachaKind × V) + 1))
  omega

lemma schedStates_stuck {s : BrachaState P V} {K : ℕ}
    (hK : ¬∃ x t, (brachaLTS f leader F).Tr (schedStates f leader F s K) (some x) t ∧
      x ∈ (schedStates f leader F s K).sent) (m : ℕ) :
    schedStates f leader F s (K + m) = schedStates f leader F s K := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (schedStep f leader F (schedStates f leader F s (K + m))).2 = _
    rw [ih, schedStep_of_stuck f leader F hK]

/-- **Fair executions exist.** With finitely many values, every state starts a fair infinite
execution. -/
theorem exists_fair_execution [Fintype V] (s : BrachaState P V) :
    ∃ (ss : ωSequence (BrachaState P V)) (μs : ωSequence (Option (P × P × BrachaKind × V))),
      (brachaLTS f leader F).OmegaExecution ss μs ∧ ss 0 = s ∧ BrachaFair F ss := by
  refine ⟨schedStates f leader F s, schedLabels f leader F s, schedStates_exec f leader F s, rfl,
    ?_⟩
  obtain ⟨K, hK⟩ := exists_stuck (f := f) (leader := leader) (F := F) s
  intro k p j m hm hj
  refine ⟨K, ?_⟩
  by_contra hnot
  -- The message is still pending in the stuck state, so the scheduler is not stuck.
  have hmono : ∀ a b, a ≤ b →
      (schedStates f leader F s a).sent ⊆ (schedStates f leader F s b).sent := by
    intro a b hab
    induction hab with
    | refl => exact subset_rfl
    | step _ ih => exact ih.trans (sent_subset_of_tr (schedStep_tr f leader F _))
  have hm' : (p, j, m) ∈ (schedStates f leader F s K).sent := by
    have := hmono k (K + k) (Nat.le_add_left k K) hm
    rwa [schedStates_stuck hK k] at this
  exact hK ⟨(p, j, m), _, ⟨hj, Or.inr hm', hnot, rfl⟩, hm'⟩

end Scheduler

/-! ### Consequences and boundary cases -/

/-- With a non-faulty leader and finitely many values, the scheduled execution is fair, so every
non-faulty party delivers the leader's input in it. -/
example [Fintype V] (f : ℕ) (hf : 3 * f < Fintype.card P) (F : Finset P) (hF : #F ≤ f)
    (leader : P) (hl : leader ∉ F) (input : V) :
    ∃ ss : ωSequence (BrachaState P V), ss 0 = brachaStart leader input F ∧
      ∀ i ∉ F, ∃ k, (ss k).delivered i = some input := by
  obtain ⟨ss, μs, h, h0, hfair⟩ :=
    exists_fair_execution (f := f) (leader := leader) (F := F) (brachaStart leader input F)
  exact ⟨ss, h0, (bracha_reliable_broadcast f hf F hF leader input).1 hl ss μs h h0 hfair⟩

/-- The theorem applies to four parties with one fault. -/
example (F : Finset (Fin 4)) (hF : #F ≤ 1) (leader : Fin 4) (input : Bool) :=
  bracha_reliable_broadcast 1 (by simp) F hF leader input

/-- The execution that only stutters from the initial state. -/
def idle (leader : P) (input : V) (F : Finset P) : ωSequence (BrachaState P V) :=
  (fun _ => brachaStart leader input F : ℕ → BrachaState P V)

lemma idle_exec (f : ℕ) (leader : P) (input : V) (F : Finset P) :
    (brachaLTS f leader F).OmegaExecution (idle leader input F)
      ((fun _ => none : ℕ → Option (P × P × BrachaKind × V)) : ωSequence _) :=
  fun _ => rfl

/-- A faulty leader may stay silent: the stuttering execution is then fair and no party ever
delivers, so validity needs a non-faulty leader, and totality only says that all non-faulty
parties deliver if one does. -/
example (leader : P) (input : V) (F : Finset P) (hl : leader ∈ F) :
    BrachaFair F (idle leader input F) ∧ ∀ k i, (idle leader input F k).delivered i = none := by
  refine ⟨fun k p j m hm _ => ?_, fun _ _ => rfl⟩
  simp [idle, brachaStart, hl] at hm

/-- With a non-faulty leader, the stuttering execution is not fair: the leader's proposal is
never received. -/
example (leader : P) (input : V) (F : Finset P) (hl : leader ∉ F) :
    ¬BrachaFair F (idle leader input F) := by
  intro hfair
  obtain ⟨k, hk⟩ := hfair 0 leader leader (.init, input) (by simp [idle, brachaStart, hl]) hl
  simp [idle, brachaStart] at hk

/-- The bound $n > 3f$ cannot be dropped. With three parties and $f = 1$, so that $n = 3f$, a
faulty leader `0` makes the non-faulty parties `1` and `2` deliver different values: it proposes
`true` to `1` and `false` to `2`, and adds its own echo and vote to those of each, which reaches
the thresholds $n - f = f + 1 = 2$ for both. -/
example : ∃ s, (brachaLTS (V := Bool) 1 (0 : Fin 3) {0}).CanReach (brachaStart 0 true {0}) s ∧
    s.delivered 1 = some true ∧ s.delivered 2 = some false := by
  refine ⟨?s, ⟨[some (0, 1, .init, true),
      some (0, 2, .init, false),
      some (1, 1, .echo, true),
      some (0, 1, .echo, true),
      some (2, 2, .echo, false),
      some (0, 2, .echo, false),
      some (1, 1, .vote, true),
      some (0, 1, .vote, true),
      some (2, 2, .vote, false),
      some (0, 2, .vote, false)], ?run⟩, ?d1, ?d2⟩
  case run =>
    refine .stepL ⟨?_, ?_, ?_, rfl⟩ ?_
    · decide
    · exact Or.inl (by decide)
    · simp [brachaStart]
    refine .stepL ⟨?_, ?_, ?_, rfl⟩ ?_
    · decide
    · exact Or.inl (by decide)
    · simp [brachaStart]
    refine .stepL ⟨?_, ?_, ?_, rfl⟩ ?_
    · decide
    · exact Or.inr (by simp [brachaStart])
    · simp [brachaStart]
    refine .stepL ⟨?_, ?_, ?_, rfl⟩ ?_
    · decide
    · exact Or.inl (by decide)
    · simp [brachaStart]
    refine .stepL ⟨?_, ?_, ?_, rfl⟩ ?_
    · decide
    · exact Or.inr (by simp [brachaStart])
    · simp [brachaStart]
    refine .stepL ⟨?_, ?_, ?_, rfl⟩ ?_
    · decide
    · exact Or.inl (by decide)
    · simp [brachaStart]
    refine .stepL ⟨?_, ?_, ?_, rfl⟩ ?_
    · decide
    · right
      simp [brachaStart]
      decide
    · simp [brachaStart]
    refine .stepL ⟨?_, ?_, ?_, rfl⟩ ?_
    · decide
    · exact Or.inl (by decide)
    · simp [brachaStart]
    refine .stepL ⟨?_, ?_, ?_, rfl⟩ ?_
    · decide
    · right
      simp [brachaStart]
      decide
    · simp [brachaStart]
    refine .stepL ⟨?_, ?_, ?_, rfl⟩ ?_
    · decide
    · exact Or.inl (by decide)
    · simp [brachaStart]
    exact .refl
  · simp [brachaStart]
    decide
  · simp [brachaStart]
    decide

end Cslib.Distributed.Byzantine.BrachaBroadcast.Tests
