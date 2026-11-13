/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card

@[expose] public section



/-- Majority quorums intersect: any two subsets of a finite set
each containing more than half the elements share an element. -/
theorem majority_intersect {A : Type*} [Fintype A] [DecidableEq A]
    (S T : Finset A)
    (hS : Fintype.card A < 2 * S.card) (hT : Fintype.card A < 2 * T.card) :
    (S ∩ T).Nonempty := by
  have h1 := Finset.card_inter_add_card_union S T
  have h2 := Finset.card_le_card (Finset.subset_univ (S ∪ T))
  rw [Finset.card_univ] at h2
  have hpos : 0 < (S ∩ T).card := by omega
  exact Finset.card_pos.mp hpos

/-- The Paxos proposal-safety step. Acceptors' latest accepted
(ballot, value) pairs are given by `acc`. A value `v` was
accepted at ballot `b` by a majority `M`. A proposer at a later
ballot `b' > b` reads a majority quorum `Q` whose members'
accepted ballots are all below `b'` (they have promised `b'`),
and — the induction hypothesis of the full safety proof — every
value accepted within `Q` at a ballot in `[b, b')` is already
known to be `v`. Then the quorum read is safe: some member of
`Q` still holds `(b, v)`, and every accepted entry in `Q` at a
ballot `≥ b` has value `v`; in particular the highest-ballot
accepted value in `Q`, which the proposer must propose, is `v`.
Iterating this step over ballots is the Synod safety proof. -/
theorem proposal_safety_step {n : ℕ} {V : Type*}
    (acc : Fin n → Option (ℕ × V))
    {b b' : ℕ} (hb : b < b') {v : V}
    (M : Finset (Fin n)) (hM : n < 2 * M.card)
    (hMacc : ∀ a ∈ M, acc a = some (b, v))
    (Q : Finset (Fin n)) (hQ : n < 2 * Q.card)
    (hQlt : ∀ a ∈ Q, ∀ bw : ℕ × V, acc a = some bw → bw.1 < b')
    (hlower : ∀ b'' : ℕ, ∀ w : V, b ≤ b'' → b'' < b' →
      ∀ a ∈ Q, acc a = some (b'', w) → w = v) :
    (∃ a ∈ Q, acc a = some (b, v)) ∧
      (∀ a ∈ Q, ∀ bw : ℕ × V, acc a = some bw → b ≤ bw.1 →
        bw.2 = v) := by
  have _hb' := hb
  have hM' : Fintype.card (Fin n) < 2 * M.card := by rwa [Fintype.card_fin]
  have hQ' : Fintype.card (Fin n) < 2 * Q.card := by rwa [Fintype.card_fin]
  obtain ⟨a, ha⟩ := majority_intersect M Q hM' hQ'
  rw [Finset.mem_inter] at ha
  obtain ⟨haM, haQ⟩ := ha
  constructor
  · exact ⟨a, haQ, hMacc a haM⟩
  · intro a' ha' bw hacc hbw
    obtain ⟨b'', w⟩ := bw
    exact hlower b'' w hbw (hQlt a' ha' (b'', w) hacc) a' ha' hacc
