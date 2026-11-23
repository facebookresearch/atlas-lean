/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.Paxos.Voting
public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Logic.Function.Basic

/-!
# Paxos: the single-decree algorithm is safe

The consensus ("synod") algorithm of L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4),
2001 (author's version dated 01 Nov 2001), Section 2.2, as a CSLib labelled transition system
(`Cslib.LTS`), and the proof that in every reachable state at most one value is chosen.

**Model** (Section 2.1, "the customary asynchronous, non-Byzantine model"):

* *Synchrony:* none. Actions interleave in any order; there are no clocks or timeouts.
* *Failures:* agents may stop and restart; acceptors keep `maxBal` and their acceptances
  (stable storage), proposers keep nothing, so a crash or restart changes no state and is not
  an action. No Byzantine behaviour.
* *Messages:* sent messages are kept forever in sets (`prepares`, `promises`, `proposals`); an
  action may use any sent message any number of times or never, so messages can be delayed
  without bound, duplicated, reordered or lost; they are never corrupted.

**Actions** (Phase 1 and Phase 2 of Section 2.2):

* `prepare n`: a proposer sends a prepare request numbered `n`.
* `promise a n r`: acceptor `a`, which has not responded to a prepare request numbered `n` or
  more, responds to the prepare request `n`, promising not to accept proposals numbered less than
  `n`, and reports `r`, its highest-numbered accepted proposal with number less than `n` (step
  1(b) of Section 2.2), or `none`.
* `propose n v S`: if no proposal numbered `n` has been issued and every acceptor of the quorum
  `S` responded to the prepare request `n`, a proposer issues the proposal `(n, v)`, where `v` is
  the value of the highest-numbered proposal among the responses of `S`, or arbitrary if they
  report none.
* `accept a n v`: acceptor `a` accepts the issued proposal `(n, v)` unless it responded to a
  prepare request numbered greater than `n` (rule P1a).

**Coverage.** The acceptor's response follows step 1(b) of the derivation in Section 2.2
(p. 4): "The proposal with the highest number less than n that it has accepted". The summary
of Phase 1(b) on p. 5 omits the bound ("the highest-numbered proposal (if any) that it has
accepted"). The two differ when an acceptor has accepted a proposal numbered above `n` without
having responded to a prepare request numbered `n` or more, which rule P1a allows. Executions in
which an acceptor reports such a proposal are not covered: the theorems here are about the
algorithm of Section 2.2 with the response of step 1(b). Within that algorithm the model allows
extra behaviours (an acceptor need not ignore a prepare request for a proposal it already
accepted; any quorum system replaces majorities), so it covers the variants that make those
choices. Liveness (Section 2.4) and learners (Section 2.3) are not modelled.

**Results.** `inv_of_canReach`: an inductive invariant holds in every reachable state.
`votingOfInv`: the reachable states are Paxos voting histories (`Voting`), with P2c.
`chosen_unique_of_canReach` and `proposed_of_chosen_of_canReach`: in every reachable state at
most one value is chosen, and a chosen value was proposed.
-/

@[expose] public section

namespace Cslib.Distributed.Paxos.Algorithm

variable {A V : Type*}

/-- **State of the single-decree Paxos algorithm**: the sent prepare requests, the number of
the highest prepare request each acceptor responded to, the sent promises (responses to prepare
requests), the issued proposals (accept requests), and the acceptances. -/
structure State (A V : Type*) where
  /-- Numbers of the prepare requests sent. -/
  prepares : Set ℕ
  /-- The highest-numbered prepare request each acceptor has responded to, if any. -/
  maxBal : A → Option ℕ
  /-- Responses `(a, n, r)` of acceptor `a` to the prepare request `n`, reporting `r`. -/
  promises : Set (A × ℕ × Option (ℕ × V))
  /-- Issued proposals `(n, v)`. -/
  proposals : Set (ℕ × V)
  /-- Acceptances `(a, n, v)`: acceptor `a` accepted the proposal `(n, v)`. -/
  votes : Set (A × ℕ × V)

/-- **Initial state of single-decree Paxos**: nothing sent, nothing accepted, no promise made. -/
def init : State A V := ⟨∅, fun _ => none, ∅, ∅, ∅⟩

/-- **Highest-numbered acceptance below a number.** `r` is the highest-numbered proposal with
number less than `n` that acceptor `a` accepted in `votes`, or `none` if there is none. -/
def HighestBelow (votes : Set (A × ℕ × V)) (a : A) (n : ℕ) : Option (ℕ × V) → Prop
  | none => ∀ c < n, ∀ w, (a, c, w) ∉ votes
  | some (c, w) => c < n ∧ (a, c, w) ∈ votes ∧ ∀ d w', c < d → d < n → (a, d, w') ∉ votes

/-- **Lamport's value rule** (Phase 2(a)): every response of the acceptors in `S` to the prepare
request `n` reports nothing, or `v` is the value of the highest-numbered reported proposal. -/
def SafeValue (promises : Set (A × ℕ × Option (ℕ × V))) (S : Finset A) (n : ℕ) (v : V) :
    Prop :=
  (∀ a ∈ S, ∀ r, (a, n, r) ∈ promises → r = none) ∨
    ∃ a ∈ S, ∃ c, (a, n, some (c, v)) ∈ promises ∧
      ∀ a' ∈ S, ∀ c' w', (a', n, some (c', w')) ∈ promises → c' ≤ c

/-- **Actions of single-decree Paxos**, the labels of the transition system. -/
inductive Action (A V : Type*)
  /-- A proposer sends a prepare request. -/
  | prepare (n : ℕ)
  /-- An acceptor responds to a prepare request. -/
  | promise (a : A) (n : ℕ) (r : Option (ℕ × V))
  /-- A proposer issues a proposal, justified by the responses of a quorum. -/
  | propose (n : ℕ) (v : V) (S : Finset A)
  /-- An acceptor accepts a proposal. -/
  | accept (a : A) (n : ℕ) (v : V)

variable [DecidableEq A]

/-- **One step of single-decree Paxos** (Lamport, *Paxos Made Simple*, Section 2.2, Phases 1
and 2). -/
inductive Step (Q : QuorumSystem A) : State A V → Action A V → State A V → Prop
  | prepare (s : State A V) (n : ℕ) :
      Step Q s (.prepare n) { s with prepares := insert n s.prepares }
  | promise (s : State A V) (a : A) (n : ℕ) (r : Option (ℕ × V)) :
      n ∈ s.prepares → (∀ k, s.maxBal a = some k → k < n) → HighestBelow s.votes a n r →
      Step Q s (.promise a n r)
        { s with maxBal := Function.update s.maxBal a (some n),
                 promises := insert (a, n, r) s.promises }
  | propose (s : State A V) (n : ℕ) (v : V) (S : Finset A) :
      (∀ w, (n, w) ∉ s.proposals) → Q.IsQuorum S → (∀ a ∈ S, ∃ r, (a, n, r) ∈ s.promises) →
      SafeValue s.promises S n v →
      Step Q s (.propose n v S) { s with proposals := insert (n, v) s.proposals }
  | accept (s : State A V) (a : A) (n : ℕ) (v : V) :
      (n, v) ∈ s.proposals → (∀ k, s.maxBal a = some k → k ≤ n) →
      Step Q s (.accept a n v) { s with votes := insert (a, n, v) s.votes }

/-- **Single-decree Paxos as a CSLib labelled transition system.** -/
def lts (Q : QuorumSystem A) : Cslib.LTS (State A V) (Action A V) := ⟨Step Q⟩

/-- **Chosen value in a state** (Section 2.2): every acceptor of some quorum accepted a proposal
with value `v`, all with the same number. -/
def ValueChosen (Q : QuorumSystem A) (s : State A V) (v : V) : Prop :=
  ∃ b C, Q.IsQuorum C ∧ ∀ a ∈ C, (a, b, v) ∈ s.votes

/-- **The inductive invariant of single-decree Paxos.** Acceptances are of issued proposals;
proposal numbers are unique; an acceptor that responded to the prepare request `n` has
`maxBal ≥ n` and its report is still its highest acceptance below `n`; every issued proposal
is justified by responses of a quorum under the value rule. -/
structure Inv (Q : QuorumSystem A) (s : State A V) : Prop where
  votes_proposed : ∀ a b v, (a, b, v) ∈ s.votes → (b, v) ∈ s.proposals
  unique : ∀ b v w, (b, v) ∈ s.proposals → (b, w) ∈ s.proposals → v = w
  promise_bal : ∀ a n r, (a, n, r) ∈ s.promises → ∃ k, s.maxBal a = some k ∧ n ≤ k
  promise_highest : ∀ a n r, (a, n, r) ∈ s.promises → HighestBelow s.votes a n r
  proposal_safe : ∀ n v, (n, v) ∈ s.proposals → ∃ S, Q.IsQuorum S ∧
    (∀ a ∈ S, ∃ r, (a, n, r) ∈ s.promises) ∧ SafeValue s.promises S n v

omit [DecidableEq A] in
theorem highestBelow_insert {votes : Set (A × ℕ × V)} {a a' : A} {b n : ℕ} {v : V}
    (h : a' = a → n ≤ b) (r : Option (ℕ × V)) :
    HighestBelow (insert (a, b, v) votes) a' n r ↔ HighestBelow votes a' n r := by
  have key : ∀ d w, d < n → ((a', d, w) ∈ insert (a, b, v) votes ↔ (a', d, w) ∈ votes) := by
    intro d w hd
    simp only [Set.mem_insert_iff, Prod.mk.injEq, or_iff_right_iff_imp]
    rintro ⟨rfl, rfl, rfl⟩
    exact absurd (h rfl) (by omega)
  rcases r with _ | ⟨c, w⟩
  · simp only [HighestBelow]
    exact forall₂_congr fun c hc => forall_congr' fun w => not_congr (key c w hc)
  · simp only [HighestBelow]
    constructor
    · rintro ⟨hc, hv, hgap⟩
      exact ⟨hc, (key c w hc).mp hv, fun d w' h1 h2 => by rw [← key d w' h2]; exact hgap d w' h1 h2⟩
    · rintro ⟨hc, hv, hgap⟩
      exact ⟨hc, (key c w hc).mpr hv, fun d w' h1 h2 => by rw [key d w' h2]; exact hgap d w' h1 h2⟩

omit [DecidableEq A] in
/-- **The Paxos invariant holds initially.** -/
theorem inv_init (Q : QuorumSystem A) : Inv Q (init : State A V) where
  votes_proposed := by simp [init]
  unique := by simp [init]
  promise_bal := by simp [init]
  promise_highest := by simp [init]
  proposal_safe := by simp [init]

/-- **Every step of single-decree Paxos preserves the invariant.** -/
theorem inv_step {Q : QuorumSystem A} {s s' : State A V} {μ : Action A V}
    (hs : Inv Q s) (h : Step Q s μ s') : Inv Q s' := by
  cases h with
  | prepare n => exact ⟨hs.1, hs.2, hs.3, hs.4, hs.5⟩
  | promise a n r hn hmay hhigh =>
    -- a new response for `n` from `a` is the first one: earlier responses of `a` are for
    -- numbers at most `maxBal a < n`
    have hfresh : ∀ r', (a, n, r') ∉ s.promises := by
      intro r' hr'
      obtain ⟨k, hk, hnk⟩ := hs.promise_bal a n r' hr'
      exact absurd (hmay k hk) (by omega)
    refine ⟨hs.votes_proposed, hs.unique, ?_, ?_, ?_⟩
    · intro a' n' r' hmem
      rcases Set.mem_insert_iff.mp hmem with heq | hold
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact ⟨n', by simp, le_rfl⟩
      · obtain ⟨k, hk, hnk⟩ := hs.promise_bal a' n' r' hold
        by_cases ha : a' = a
        · subst ha
          exact ⟨n, by simp, by have := hmay k hk; omega⟩
        · exact ⟨k, by simp [Function.update_of_ne ha, hk], hnk⟩
    · intro a' n' r' hmem
      rcases Set.mem_insert_iff.mp hmem with heq | hold
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact hhigh
      · exact hs.promise_highest a' n' r' hold
    · intro m v hv
      obtain ⟨S, hS, hresp, hsafe⟩ := hs.proposal_safe m v hv
      refine ⟨S, hS, fun a' ha' => ?_, ?_⟩
      · obtain ⟨r', hr'⟩ := hresp a' ha'
        exact ⟨r', Set.mem_insert_of_mem _ hr'⟩
      · -- the new response is not for `m` from a member of `S`, so the value rule is unchanged
        have hnot : ∀ a' ∈ S, ∀ r', (a', m, r') ≠ (a, n, r) := by
          intro a' ha' r' heq
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl, -⟩ := heq
          obtain ⟨r'', hr''⟩ := hresp a' ha'
          exact hfresh r'' hr''
        rcases hsafe with hnone | ⟨a₀, ha₀, c, hc, hmax⟩
        · refine Or.inl fun a' ha' r' hr' => ?_
          rcases Set.mem_insert_iff.mp hr' with heq | hold
          · exact absurd heq (hnot a' ha' r')
          · exact hnone a' ha' r' hold
        · refine Or.inr ⟨a₀, ha₀, c, Set.mem_insert_of_mem _ hc, fun a' ha' c' w' hr' => ?_⟩
          rcases Set.mem_insert_iff.mp hr' with heq | hold
          · exact absurd heq (hnot a' ha' _)
          · exact hmax a' ha' c' w' hold
  | propose n v S hnew hS hresp hsafe =>
    refine ⟨fun a b w hw => Set.mem_insert_of_mem _ (hs.votes_proposed a b w hw), ?_, hs.3, hs.4,
      ?_⟩
    · intro b w w' hw hw'
      rcases Set.mem_insert_iff.mp hw with h1 | h1 <;>
        rcases Set.mem_insert_iff.mp hw' with h2 | h2
      · simp only [Prod.mk.injEq] at h1 h2
        rw [h1.2, h2.2]
      · simp only [Prod.mk.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        exact absurd h2 (hnew w')
      · simp only [Prod.mk.injEq] at h2
        obtain ⟨rfl, -⟩ := h2
        exact absurd h1 (hnew w)
      · exact hs.unique b w w' h1 h2
    · intro m w hw
      rcases Set.mem_insert_iff.mp hw with h1 | h1
      · simp only [Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact ⟨S, hS, hresp, hsafe⟩
      · exact hs.proposal_safe m w h1
  | accept a n v hprop hmay =>
    refine ⟨?_, hs.unique, hs.promise_bal, ?_, hs.proposal_safe⟩
    · intro a' b w hw
      rcases Set.mem_insert_iff.mp hw with h1 | h1
      · simp only [Prod.mk.injEq] at h1
        obtain ⟨-, rfl, rfl⟩ := h1
        exact hprop
      · exact hs.votes_proposed a' b w h1
    · intro a' n' r' hr'
      refine (highestBelow_insert (fun ha => ?_) r').mpr (hs.promise_highest a' n' r' hr')
      subst ha
      obtain ⟨k, hk, hnk⟩ := hs.promise_bal a' n' r' hr'
      exact hnk.trans (hmay k hk)

/-- **The Paxos invariant holds in every reachable state.** -/
theorem inv_of_canReach {Q : QuorumSystem A} {s : State A V} (h : (lts Q).CanReach init s) :
    Inv Q s := by
  obtain ⟨μs, hμs⟩ := h
  exact Cslib.LTS.mtrInv_of_trInv (lts := lts Q) (p := Inv Q)
    (fun _ _ _ hstep hs => inv_step hs hstep) _ _ _ hμs (inv_init Q)

/-- **Reachable states are Paxos voting histories.** In every state satisfying the invariant,
the issued proposals and the acceptances form a `Voting` history: in particular they satisfy
Lamport's condition P2c over the whole history. -/
def votingOfInv {Q : QuorumSystem A} {s : State A V} (hs : Inv Q s) : Voting Q V where
  proposed b v := (b, v) ∈ s.proposals
  voted a b v := (a, b, v) ∈ s.votes
  unique := hs.unique
  voted_proposed := hs.votes_proposed
  p2c b v hv := by
    obtain ⟨S, hS, hresp, hsafe⟩ := hs.proposal_safe b v hv
    refine ⟨S, hS, ?_⟩
    rcases hsafe with hnone | ⟨a₀, ha₀, c, hc, hmax⟩
    · refine Or.inl fun a ha => ?_
      obtain ⟨r, hr⟩ := hresp a ha
      have := hs.promise_highest a b r hr
      rw [hnone a ha r hr] at this
      exact this
    · obtain ⟨hcb, hvote, -⟩ := hs.promise_highest a₀ b _ hc
      refine Or.inr ⟨c, hcb, ⟨a₀, ha₀, hvote⟩, fun a ha d w hcd hdb => ?_⟩
      obtain ⟨r, hr⟩ := hresp a ha
      have hh := hs.promise_highest a b r hr
      rcases r with _ | ⟨c', w'⟩
      · exact hh d hdb w
      · exact hh.2.2 d w (lt_of_le_of_lt (hmax a ha c' w' hr) hcd) hdb

/-- **Paxos safety: at most one value is chosen** (Lamport, *Paxos Made Simple*, Section 2.1,
second safety requirement, proved as in Section 2.2). In every reachable state of the
single-decree algorithm, two chosen values are equal. Acceptances are never withdrawn, so a
value chosen once stays chosen and no other value is ever chosen later in the same run. -/
theorem chosen_unique_of_canReach {Q : QuorumSystem A} {s : State A V}
    (h : (lts Q).CanReach init s) {v w : V} (hv : ValueChosen Q s v) (hw : ValueChosen Q s w) :
    v = w :=
  (votingOfInv (inv_of_canReach h)).chosen_unique hv hw

/-- **Paxos safety: only a proposed value is chosen** (Lamport, *Paxos Made Simple*, Section 2.1,
first safety requirement). -/
theorem proposed_of_chosen_of_canReach {Q : QuorumSystem A} {s : State A V}
    (h : (lts Q).CanReach init s) {v : V} (hv : ValueChosen Q s v) : ∃ b, (b, v) ∈ s.proposals :=
  (votingOfInv (inv_of_canReach h)).proposed_of_chosen hv

end Cslib.Distributed.Paxos.Algorithm
