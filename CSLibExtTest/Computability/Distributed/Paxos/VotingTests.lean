/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.Paxos.Voting

/-!
# Tests for the Paxos voting argument

A voting history over three acceptors with majority quorums, in which the single proposal
`(1, 7)` is accepted by the acceptors `0` and `1`. Its conditions hold (P2c by its clause (a):
nothing was accepted below `1`), the value `7` is chosen, and so no other value is.
-/

@[expose] public section

namespace Cslib.Distributed.Paxos.VotingTests

/-- One proposal, `(1, 7)`, accepted by the majority `{0, 1}` of three acceptors. -/
def H : Voting (QuorumSystem.majority (Fin 3)) ℕ where
  proposed b v := b = 1 ∧ v = 7
  voted a b v := a ≠ 2 ∧ b = 1 ∧ v = 7
  unique _ _ _ h₁ h₂ := h₁.2.trans h₂.2.symm
  voted_proposed _ _ _ h := h.2
  p2c b v _ := ⟨{0, 1}, by change Fintype.card (Fin 3) < 2 * Finset.card _; decide,
    Or.inl fun _ _ c hc _ h => by omega⟩

theorem chosen_seven : H.chosen 7 :=
  ⟨1, {0, 1}, by change Fintype.card (Fin 3) < 2 * Finset.card _; decide, by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> exact ⟨by decide, rfl, rfl⟩⟩

example (w : ℕ) (hw : H.chosen w) : w = 7 := H.chosen_unique hw chosen_seven

example : ∃ b, H.proposed b 7 := H.proposed_of_chosen chosen_seven

end Cslib.Distributed.Paxos.VotingTests
