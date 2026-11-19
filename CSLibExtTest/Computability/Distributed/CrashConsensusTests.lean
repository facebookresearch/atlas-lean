/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.CrashConsensusRounds

/-!
# Tests for synchronous consensus with crash failures

* Delivery: a process crashing in round `1` with recipients `{1}` delivers all its round-`0`
  messages, only its round-`1` message to process `1`, and nothing afterwards.
* Positive control: with no crash, every process adopting the value of process `0` solves
  consensus in one round, so `Solves` is satisfiable.
* A crash breaks it: if process `0` crashes in round `0` and reaches only process `1`, processes
  `1` and `2` disagree.
* `not_solves_zero` applies to it.
* The crash pattern `crash01` is admissible for two rounds (one crash, before round `2`), and
  a pattern with two crashes in the same round is not.
* The `f + 1` round bound: no protocol for three processes solves consensus with one crash in
  one round.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.CrashConsensus.Tests

open CrashProtocol

/-- Process `0` crashes in round `1`, reaching only process `1` in that round. -/
def crash01 : CrashPattern (Fin 3) := fun j => if j = 0 then some (1, {1}) else none

example : crash01.delivers 0 0 2 = true := by decide
example : crash01.delivers 1 0 1 = true := by decide
example : crash01.delivers 1 0 2 = false := by decide
example : crash01.delivers 2 0 1 = false := by decide
example : crash01.delivers 5 1 2 = true := by decide

/-- Every process adopts the value of process `0` if it receives it, and keeps its own
otherwise. -/
def follow0 (n : ℕ) : CrashProtocol (Fin (n + 1)) Bool Bool Bool where
  init _ x := x
  send _ _ s _ := s
  recv _ _ s msg := (msg 0).getD s
  decide _ s := s

/-- With no crash, `follow0` solves consensus in one round. -/
theorem follow0_solves (n : ℕ) : (follow0 n).Solves 0 1 := by
  intro x π hπ
  have hnone : ∀ j, π j = none := by
    intro j
    by_contra h
    have : j ∈ π.faulty := by simpa [CrashPattern.faulty, Option.ne_none_iff_isSome] using h
    exact absurd (Finset.card_pos.2 ⟨j, this⟩) (by omega)
  have hdec : ∀ i, (follow0 n).decision x π 1 i = x 0 := by
    intro i
    simp [decision, state, follow0, CrashPattern.delivers_of_eq_none (hnone 0)]
  exact ⟨fun i j _ _ => by rw [hdec, hdec], fun i _ => ⟨0, (hdec i).symm⟩⟩

/-- Process `0` crashes in round `0`, reaching only process `1`. -/
def crash00 : CrashPattern (Fin 3) := fun j => if j = 0 then some (0, {1}) else none

/-- Under `crash00`, process `1` adopts the input of process `0` and process `2` keeps its own:
with inputs `true, false, false` they disagree. -/
example :
    (follow0 2).decision (fun j => decide (j = 0)) crash00 1 1 ≠
      (follow0 2).decision (fun j => decide (j = 0)) crash00 1 2 := by
  decide

/-- `not_solves_zero` applies to `follow0`. -/
example (n : ℕ) : ¬ (follow0 (n + 1)).Solves 0 0 :=
  (follow0 (n + 1)).not_solves_zero (by simp) 0

/-- `crash01` is admissible for two rounds. -/
example : crash01.Good 2 := by
  refine ⟨fun j ρ D h => ?_, fun j j' ρ D D' h h' => ?_⟩
  · by_cases hj : j = 0
    · simp [crash01, hj] at h; omega
    · simp [crash01, hj] at h
  · by_cases hj : j = 0
    · by_cases hj' : j' = 0
      · rw [hj, hj']
      · simp [crash01, hj'] at h'
    · simp [crash01, hj] at h

/-- Processes `0` and `1` both crash in round `0`. -/
def crash2 : CrashPattern (Fin 3) := fun j => if j = 2 then none else some (0, ∅)

/-- Two crashes in round `0` are not admissible. -/
example : ¬ crash2.Good 2 := by
  intro h
  exact absurd (h.2 0 1 0 ∅ ∅ (by simp [crash2]) (by simp [crash2])) (by decide)

/-- Aguilera and Toueg's form: no protocol for three processes solves consensus in one round
against one crash. -/
example {σ M : Type} (Q : CrashProtocol (Fin 3) Bool σ M) : ¬ Q.SolvesOnePerRound 1 :=
  Q.not_solvesOnePerRound (by simp)

/-- With a single process, `follow0` solves consensus in one round against one crash per round,
so `SolvesOnePerRound` is satisfiable (and the hypothesis `T + 2 ≤ n` cannot be dropped). -/
example : (follow0 0).SolvesOnePerRound 1 := by
  intro x π _
  refine ⟨fun i j _ _ => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j],
    fun i _ => ⟨0, ?_⟩⟩
  rw [Fin.fin_one_eq_zero i]
  simp only [decision, state, follow0]
  split <;> simp

/-- No protocol for three processes solves consensus with one crash in one round. -/
example {σ M : Type} (Q : CrashProtocol (Fin 3) Bool σ M) : ¬ Q.Solves 1 1 := fun h => by
  have := Q.f_add_one_le_of_solves (by simp) h
  omega

end Cslib.Distributed.CrashConsensus.Tests
