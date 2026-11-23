/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card

/-!
# Majority quorums and the Paxos proposal-safety step

The safety argument of the Paxos (Synod) consensus algorithm (L. Lamport, *Paxos made
simple*, ACM SIGACT News 32(4), 2001) rests on two facts proved here:

* `majority_intersect`: any two majorities of a finite set share an element.
* `proposal_safety_step`: if a majority accepted the proposal `(b, v)`, then a proposer at a
  later ballot that reads a majority quorum proposes `v`, given the induction hypothesis for
  the ballots in between. Iterating this step over ballots is the Synod safety proof.
-/

@[expose] public section

namespace Cslib.Distributed.PaxosSafety

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

/-- The Paxos proposal-safety step. The acceptance history `accepted a c w` records that
acceptor `a` accepted the proposal `(c, w)` (ballot `c`, value `w`) at some point. A proposer
at ballot `b'` reads a majority quorum `Q`: each member `a` promises `b'` and returns
`report a`, the highest-ballot proposal it had accepted so far, or `none`. For the members of
`Q` three properties are assumed:

* `hrep`: a report is a proposal the acceptor accepted, at a ballot below `b'`;
* `hmono` (ballot monotonicity): after promising `b'` an acceptor accepts no ballot below
  `b'`, so each of its acceptances below `b'` precedes its report and the reported ballot is
  at least as high;
* `hsafe` (the induction hypothesis of the full safety proof): every proposal accepted in `Q`
  at a ballot in `[b, b')` has value `v`.

If a majority `M` accepted `(b, v)` with `b < b'`, then some member of `Q` reports a ballot
at least `b` with value `v`, and every highest-ballot report in `Q` has value `v`. The
proposer of `b'` must propose the value of a highest-ballot report, so it proposes `v`;
iterating this step over ballots is the Synod safety proof. -/
theorem proposal_safety_step {n : ℕ} {V : Type*}
    (accepted : Fin n → ℕ → V → Prop) (report : Fin n → Option (ℕ × V))
    {b b' : ℕ} (hb : b < b') {v : V}
    (M : Finset (Fin n)) (hM : n < 2 * M.card)
    (hMacc : ∀ a ∈ M, accepted a b v)
    (Q : Finset (Fin n)) (hQ : n < 2 * Q.card)
    (hrep : ∀ a ∈ Q, ∀ c w, report a = some (c, w) → accepted a c w ∧ c < b')
    (hmono : ∀ a ∈ Q, ∀ c w, accepted a c w → c < b' →
      ∃ c' w', report a = some (c', w') ∧ c ≤ c')
    (hsafe : ∀ a ∈ Q, ∀ c w, accepted a c w → b ≤ c → c < b' → w = v) :
    (∃ a ∈ Q, ∃ c, b ≤ c ∧ report a = some (c, v)) ∧
      (∀ a₀ ∈ Q, ∀ c₀ w₀, report a₀ = some (c₀, w₀) →
        (∀ a ∈ Q, ∀ c w, report a = some (c, w) → c ≤ c₀) → w₀ = v) := by
  have hM' : Fintype.card (Fin n) < 2 * M.card := by rwa [Fintype.card_fin]
  have hQ' : Fintype.card (Fin n) < 2 * Q.card := by rwa [Fintype.card_fin]
  obtain ⟨a, ha⟩ := majority_intersect M Q hM' hQ'
  rw [Finset.mem_inter] at ha
  obtain ⟨haM, haQ⟩ := ha
  obtain ⟨c, w, hrepa, hbc⟩ := hmono a haQ b v (hMacc a haM) hb
  obtain ⟨hacc, hcb'⟩ := hrep a haQ c w hrepa
  have hw : w = v := hsafe a haQ c w hacc hbc hcb'
  refine ⟨⟨a, haQ, c, hbc, hw ▸ hrepa⟩, ?_⟩
  intro a₀ ha₀ c₀ w₀ hrep₀ hmax
  obtain ⟨hacc₀, hc₀⟩ := hrep a₀ ha₀ c₀ w₀ hrep₀
  exact hsafe a₀ ha₀ c₀ w₀ hacc₀ (le_trans hbc (hmax a haQ c w hrepa)) hc₀

end Cslib.Distributed.PaxosSafety
