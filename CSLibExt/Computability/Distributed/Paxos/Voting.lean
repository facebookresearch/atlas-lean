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
# Paxos: the voting argument for safety

The safety argument of L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4), 2001 (author's
version dated 01 Nov 2001), Section 2.2, stated over a history of proposals and acceptances.
Nothing here depends on timing, failures or message delivery: the argument is about which
proposals were issued and which acceptors accepted them, whatever the scheduling. The algorithm
that produces such histories, in the asynchronous non-Byzantine model, and the proof that it
keeps the hypotheses below invariant are in `CSLibExt.Computability.Distributed.Paxos.Algorithm`.

* `QuorumSystem`: a family of sets of acceptors any two of which intersect. Lamport uses
  majorities (`QuorumSystem.majority`) and notes the generalisation.
* `Voting`: a history, given by `proposed b v` (a proposal numbered `b` with value `v` was issued)
  and `voted a b v` (acceptor `a` accepted it), with unique proposal numbers, acceptances only of
  issued proposals, and Lamport's condition P2c over the whole history.
* `Voting.chosenAt`: a quorum accepted the proposal numbered `b` with value `v`.
* `Voting.p2b`: Lamport's P2b, proved by his induction on the proposal number.
* `Voting.chosen_unique` and `Voting.proposed_of_chosen`: at most one value is chosen, and only a
  proposed value can be chosen (the first two safety requirements of Section 2.1).
-/

@[expose] public section

namespace Cslib.Distributed.Paxos

variable {A V : Type*}

/-- **Quorum system.** A family of finite sets of acceptors, the quorums, any two of which
share an acceptor (Lamport, *Paxos Made Simple*, Section 2.2: "any two majorities have at least
one acceptor in common", and the "obvious generalization of a majority"). -/
structure QuorumSystem (A : Type*) where
  /-- The quorums. -/
  IsQuorum : Finset A → Prop
  /-- Any two quorums intersect. -/
  inter : ∀ Q₁ Q₂, IsQuorum Q₁ → IsQuorum Q₂ → ∃ a, a ∈ Q₁ ∧ a ∈ Q₂

/-- **Majorities form a quorum system** (Lamport, *Paxos Made Simple*, Section 2.2): the quorums
are the sets containing more than half of the finitely many acceptors. -/
def QuorumSystem.majority (A : Type*) [Fintype A] : QuorumSystem A where
  IsQuorum Q := Fintype.card A < 2 * Q.card
  inter Q₁ Q₂ h₁ h₂ := by
    classical
    obtain ⟨a, ha⟩ := Finset.inter_nonempty_of_card_lt_card_add_card (Finset.subset_univ Q₁)
      (Finset.subset_univ Q₂) (by rw [Finset.card_univ]; omega)
    exact ⟨a, Finset.mem_inter.mp ha⟩

/-- **A Paxos voting history** (Lamport, *Paxos Made Simple*, Section 2.2). `proposed b v` says
that a proposal numbered `b` with value `v` was issued and `voted a b v` that acceptor `a`
accepted it. Proposal numbers are natural numbers, different proposals have different numbers
(`unique`), an acceptor accepts only issued proposals (`voted_proposed`), and every issued
proposal satisfies Lamport's condition P2c: some quorum `S` either (a) accepted no proposal
numbered less than `b`, or (b) accepted, at some number `c < b`, a proposal with value `v`, and
nothing numbered strictly between `c` and `b`; that is, `v` is the value of the highest-numbered
proposal below `b` accepted by `S`. Lamport states P2c for the acceptances made before the
proposal is issued; here it is required of the whole history, the form in which his algorithm
keeps it, since acceptors promise not to accept proposals numbered below `b` afterwards (see
`Algorithm.votingOfInv`). -/
structure Voting (Q : QuorumSystem A) (V : Type*) where
  /-- A proposal with this number and value was issued. -/
  proposed : ℕ → V → Prop
  /-- The acceptor accepted the proposal with this number and value. -/
  voted : A → ℕ → V → Prop
  /-- Different proposals have different numbers. -/
  unique : ∀ b v w, proposed b v → proposed b w → v = w
  /-- Only issued proposals are accepted. -/
  voted_proposed : ∀ a b v, voted a b v → proposed b v
  /-- Lamport's condition P2c. -/
  p2c : ∀ b v, proposed b v → ∃ S, Q.IsQuorum S ∧
    ((∀ a ∈ S, ∀ c < b, ∀ w, ¬ voted a c w) ∨
      ∃ c < b, (∃ a ∈ S, voted a c v) ∧ ∀ a ∈ S, ∀ d w, c < d → d < b → ¬ voted a d w)

namespace Voting

variable {Q : QuorumSystem A} (H : Voting Q V)

/-- **Chosen proposal.** The proposal numbered `b` with value `v` is chosen when every acceptor
of some quorum accepted it (Lamport, *Paxos Made Simple*, Section 2.2: "A value is chosen when a
single proposal with that value has been accepted by a majority of the acceptors"). -/
def chosenAt (b : ℕ) (v : V) : Prop :=
  ∃ C, Q.IsQuorum C ∧ ∀ a ∈ C, H.voted a b v

/-- **Chosen value.** Some proposal with value `v` is chosen. -/
def chosen (v : V) : Prop :=
  ∃ b, H.chosenAt b v

/-- **Lamport's P2b** (*Paxos Made Simple*, Section 2.2): if the proposal numbered `m` with value
`v` is chosen, every proposal issued with a higher number `n` has value `v`. The proof is
Lamport's induction on `n`, from P2c and the intersection of quorums. -/
theorem p2b {m : ℕ} {v : V} (hm : H.chosenAt m v) :
    ∀ n, m < n → ∀ w, H.proposed n w → w = v := by
  obtain ⟨C, hC, hCv⟩ := hm
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hmn w hw
    obtain ⟨S, hS, hcase⟩ := H.p2c n w hw
    obtain ⟨a, haS, haC⟩ := Q.inter S C hS hC
    rcases hcase with hnone | ⟨c, hcn, ⟨a₀, -, ha₀⟩, hgap⟩
    · exact absurd (hCv a haC) (hnone a haS m hmn v)
    · have hmc : m ≤ c := by
        by_contra h
        exact hgap a haS m v (by omega) hmn (hCv a haC)
      rcases hmc.lt_or_eq with hlt | rfl
      · exact ih c hcn hlt w (H.voted_proposed _ _ _ ha₀)
      · exact H.unique _ _ _ (H.voted_proposed _ _ _ ha₀) (H.voted_proposed _ _ _ (hCv a haC))

/-- **At most one value is chosen** (Lamport, *Paxos Made Simple*, Section 2.1, second safety
requirement: "Only a single value is chosen"). -/
theorem chosen_unique {v w : V} (hv : H.chosen v) (hw : H.chosen w) : v = w := by
  obtain ⟨m, hm⟩ := hv
  obtain ⟨n, hn⟩ := hw
  have prop : ∀ {b u}, H.chosenAt b u → H.proposed b u := by
    rintro b u ⟨C, hC, hCu⟩
    obtain ⟨a, ha, -⟩ := Q.inter C C hC hC
    exact H.voted_proposed a b u (hCu a ha)
  rcases lt_trichotomy m n with h | rfl | h
  · exact (H.p2b hm n h w (prop hn)).symm
  · exact H.unique _ _ _ (prop hm) (prop hn)
  · exact H.p2b hn m h v (prop hm)

/-- **Only a proposed value is chosen** (Lamport, *Paxos Made Simple*, Section 2.1, first safety
requirement). -/
theorem proposed_of_chosen {v : V} (hv : H.chosen v) : ∃ b, H.proposed b v := by
  obtain ⟨b, C, hC, hCv⟩ := hv
  obtain ⟨a, ha, -⟩ := Q.inter C C hC hC
  exact ⟨b, H.voted_proposed a b v (hCv a ha)⟩

end Voting

end Cslib.Distributed.Paxos
