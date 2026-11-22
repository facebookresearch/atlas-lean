/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.PaxosSafety

/-!
# Tests for majority quorums and the Paxos proposal-safety step

* Two majorities of a 3-element set intersect.
* A later Paxos state in which a member of the read quorum has moved past the chosen ballot.
  Acceptors `0` and `1` (a majority of three) accepted `(1, 7)`; acceptor `1` later accepted
  `(2, 7)`. The proposer of ballot `3` reads `Q = {1, 2}`: acceptor `1` reports `(2, 7)` and
  acceptor `2` has accepted nothing. No member of `Q` still reports `(1, 7)`, yet the safety
  step applies.
-/

@[expose] public section

namespace Cslib.Distributed.PaxosSafety.Tests

/-- Boundary check: two majorities of a 3-element set intersect. -/
example (S T : Finset (Fin 3)) (hS : 3 < 2 * S.card)
    (hT : 3 < 2 * T.card) : (S ∩ T).Nonempty :=
  majority_intersect S T hS hT

/-- The acceptance history of the scenario. -/
private def laterHistory (a : Fin 3) (c w : ℕ) : Prop :=
  (a = 0 ∧ c = 1 ∧ w = 7) ∨ (a = 1 ∧ c = 1 ∧ w = 7) ∨ (a = 1 ∧ c = 2 ∧ w = 7)

/-- The reports to the proposer of ballot `3`. -/
private def laterReport : Fin 3 → Option (ℕ × ℕ)
  | 0 => some (1, 7)
  | 1 => some (2, 7)
  | 2 => none

/-- No member of the read quorum still reports the chosen pair `(1, 7)`. -/
example : ¬ ∃ a ∈ ({1, 2} : Finset (Fin 3)), laterReport a = some (1, 7) := by
  decide

/-- The read quorum contains a report of value `7` at a ballot at least `1`, and every
highest-ballot report in it has value `7`. -/
example :
    (∃ a ∈ ({1, 2} : Finset (Fin 3)), ∃ c, 1 ≤ c ∧ laterReport a = some (c, 7)) ∧
      (∀ a₀ ∈ ({1, 2} : Finset (Fin 3)), ∀ c₀ w₀, laterReport a₀ = some (c₀, w₀) →
        (∀ a ∈ ({1, 2} : Finset (Fin 3)), ∀ c w, laterReport a = some (c, w) → c ≤ c₀) →
          w₀ = 7) := by
  refine proposal_safety_step laterHistory laterReport (b := 1) (b' := 3) (by decide)
    {0, 1} (by decide) ?_ {1, 2} (by decide) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> simp [laterHistory]
  · intro a ha c w hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · simp only [laterReport, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      simp [laterHistory]
    · simp [laterReport] at hr
  · intro a ha c w hacc hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · refine ⟨2, 7, rfl, ?_⟩
      rcases hacc with ⟨h, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
      · exact absurd h (by decide)
      · decide
      · decide
    · rcases hacc with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
  · intro a ha c w hacc _ _
    rcases hacc with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

end Cslib.Distributed.PaxosSafety.Tests
