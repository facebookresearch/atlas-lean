/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bracha's Byzantine reliable broadcast
-/
module

public import Cslib.Foundations.Semantics.LTS.OmegaExecution
public import Mathlib.Data.Fintype.Card

/-!
# Bracha's Byzantine reliable broadcast

Bracha's protocol lets a designated leader broadcast its input to `n` parties over
authenticated asynchronous point-to-point channels when at most `f` parties are Byzantine and
`n > 3 f`:

* the leader sends `⟨v⟩` to all parties;
* on receiving `⟨v⟩` from the leader, a party sends `⟨echo, v⟩` to all, unless it has already
  sent an echo;
* a party sends `⟨vote, v⟩` to all, unless it has already sent a vote, after receiving
  `⟨echo, v⟩` from `n - f` distinct parties or `⟨vote, v⟩` from `f + 1` distinct parties;
* a party delivers `v` on receiving `⟨vote, v⟩` from `n - f` distinct parties, unless it has
  already delivered a value.

It satisfies validity (with a non-faulty leader, every non-faulty party eventually delivers
the leader's input), agreement (non-faulty parties that deliver deliver the same value) and
totality (if a non-faulty party delivers, every non-faulty party eventually delivers).

## Model

* **Parties and faults:** a finite type `P` of `n` parties, a leader, and a fixed set `F` of
  at most `f` faulty parties. The thresholds `n - f` and `f + 1` use the parameter `f`.
* **Transition system:** `brachaLTS`, a labelled transition system in CSLib's sense. A state
  records the messages the non-faulty parties have sent, the messages each party has received
  together with their senders, and the values each party has echoed, voted for and delivered.
  A step is either a stuttering step or the receipt of one message by a non-faulty party, which
  then applies the rules of the protocol at once.
* **Byzantine parties:** a faulty party may send any message to any party at any time, but
  only under its own name, since the channels are authenticated: a step may hand any message
  from a faulty sender to a non-faulty party. Faulty parties need no local state, and
  stuttering steps make every finite execution extendable to an infinite one.
* **Asynchrony and fairness:** messages arrive in any order and after any delay. An infinite
  execution is fair (`BrachaFair`) when every message sent to a non-faulty party is eventually
  received by it. Nothing constrains when, or whether, a faulty party's messages arrive.

## Proof

Agreement holds in every reachable state by an inductive invariant. Each vote of a party is
backed by `n - f` echoes for its value received by some party: either its own, or, for a vote
cast after `f + 1` votes, those backing the vote of a non-faulty voter among them. Two sets of
`n - f` parties share a non-faulty party, which echoes at most once, so no two parties vote for
different values. A delivered value has `n - f > f` votes, one of them non-faulty, so delivered
values agree too.

Validity and totality follow in fair executions. With a non-faulty leader every non-faulty
party receives its input, echoes it, receives `n - f` echoes for it and votes for it; every
vote is for the input, so every non-faulty party receives `n - f` votes for it and delivers it.
If a non-faulty party delivers `v`, at least `n - 2 f ≥ f + 1` non-faulty parties voted for
`v`; every non-faulty party receives these votes and votes, necessarily for `v`, and then
receives `n - f` votes for `v` and delivers.

## Main definitions

* `brachaLTS`: the protocol as a transition system, for given `f`, leader and faulty parties,
  on the global states `BrachaState` and messages built from `BrachaKind`.
* `brachaStart`: the initial state, for a given input of the leader.
* `BrachaFair`: fairness of an infinite execution.

## Main results

* `bracha_reliable_broadcast`: validity, agreement and totality, for `n > 3 f` and at most `f`
  faulty parties.

## References

* I. Abraham, K. Nayak, *Living with asynchrony: Bracha's reliable broadcast*, Decentralized
  Thoughts, 19 September 2020: the properties, the protocol and the proofs of Claims 1 to 3.
* G. Bracha, *Asynchronous Byzantine agreement protocols*, Information and Computation 75(2),
  1987, 130–143, doi:10.1016/0890-5401(87)90054-X.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.Byzantine

open Finset

/- The kinds of messages of Bracha's broadcast. A message is a pair `(k, v)` of a kind `k` and a
value `v`: the leader's proposal `⟨v⟩` (kind `init`), an echo `⟨echo, v⟩` (kind `echo`) or a vote
`⟨vote, v⟩` (kind `vote`). -/
inductive BrachaKind where
  /-- The leader's proposal `⟨v⟩`. -/
  | init
  /-- An echo `⟨echo, v⟩`. -/
  | echo
  /-- A vote `⟨vote, v⟩`. -/
  | vote
  deriving DecidableEq

instance : Fintype BrachaKind := ⟨{.init, .echo, .vote}, fun k => by cases k <;> simp⟩

/- The global states of Bracha's broadcast, for parties `P` and values `V`: a set of triples
`(p, j, m)`, read as: `p` has sent `m` to `j` (the transition system records only the sends of
non-faulty parties); for each party `i`, the finite set of pairs `(q, m)` such that `i` has
received `m` from `q`; and the value, if any, that `i` has echoed, voted for and delivered. -/
structure BrachaState (P V : Type*) where
  /-- Triples `(p, j, m)`, read as: `p` has sent `m` to `j`. The transition system records only
  the sends of non-faulty parties. -/
  sent : Set (P × P × BrachaKind × V)
  /-- The pairs `(q, m)` such that party `i` has received `m` from `q`. -/
  rcvd : P → Finset (P × BrachaKind × V)
  /-- The value that party `i` has echoed, if any. -/
  echoed : P → Option V
  /-- The value that party `i` has voted for, if any. -/
  voted : P → Option V
  /-- The value that party `i` has delivered, if any. -/
  delivered : P → Option V

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]

/-- **Bracha's broadcast as a transition system.** Let $n$ be the number of parties, $f$ a
natural number, `leader` the designated leader and $F$ the set of faulty parties. A message is a
pair $(k, v)$ of a kind $k$, which is `init` (the leader's proposal), `echo` or `vote`, and a
value $v$. A state records a set of triples $(p, j, m)$, read as: $p$ has sent $m$ to $j$ (the
transition system records only the sends of non-faulty parties); for each party $i$, the pairs
$(q, m)$ such that $i$ has received $m$ from $q$; and the value, if any, that $i$ has echoed,
voted for and delivered.

A stuttering step (label `none`) changes nothing. A step labelled $(q, i, (k, v))$ lets a
non-faulty party $i$ receive the message $(k, v)$ from $q$ for the first time. It is possible
when $q$ has sent $(k, v)$ to $i$, or when $q$ is faulty: a faulty party may send any message to
anyone at any time, but only under its own name, as the channels are authenticated. Let $r$ be
the messages $i$ has received, this one included. In the step, $i$

* echoes $v$, sending $(\mathrm{echo}, v)$ to every party, if it has not echoed yet, $k$ is
  `init` and $q$ is the leader;
* votes for $v$, sending $(\mathrm{vote}, v)$ to every party, if it has not voted yet and $r$
  holds $(\mathrm{echo}, v)$ from at least $n - f$ parties or $(\mathrm{vote}, v)$ from at least
  $f + 1$ parties;
* delivers $v$ if it has not delivered yet and $r$ holds $(\mathrm{vote}, v)$ from at least
  $n - f$ parties.

Nothing else changes. Here $n - f$ is truncated subtraction, $0$ when $f \ge n$. -/
def brachaLTS (f : ℕ) (leader : P) (F : Finset P) :
    LTS (BrachaState P V) (Option (P × P × BrachaKind × V)) where
  Tr s a t := match a with
    | none => t = s
    | some (q, i, k, v) =>
      i ∉ F ∧ (q ∈ F ∨ (q, i, k, v) ∈ s.sent) ∧ (q, k, v) ∉ s.rcvd i ∧
      t = { sent := s.sent ∪ {x | x.1 = i ∧
              (s.echoed i = none ∧ k = .init ∧ q = leader ∧ x.2.2 = (.echo, v) ∨
                s.voted i = none ∧
                  (Fintype.card P - f ≤ #{p | (p, .echo, v) ∈ insert (q, k, v) (s.rcvd i)} ∨
                    f + 1 ≤ #{p | (p, .vote, v) ∈ insert (q, k, v) (s.rcvd i)}) ∧
                  x.2.2 = (.vote, v))}
            rcvd := Function.update s.rcvd i (insert (q, k, v) (s.rcvd i))
            echoed := Function.update s.echoed i
              (if s.echoed i = none ∧ k = .init ∧ q = leader then some v else s.echoed i)
            voted := Function.update s.voted i
              (if s.voted i = none ∧
                  (Fintype.card P - f ≤ #{p | (p, .echo, v) ∈ insert (q, k, v) (s.rcvd i)} ∨
                    f + 1 ≤ #{p | (p, .vote, v) ∈ insert (q, k, v) (s.rcvd i)})
                then some v else s.voted i)
            delivered := Function.update s.delivered i
              (if s.delivered i = none ∧
                  Fintype.card P - f ≤ #{p | (p, .vote, v) ∈ insert (q, k, v) (s.rcvd i)}
                then some v else s.delivered i) }

/- The initial state of Bracha's broadcast, for a leader with input `input` and a set `F` of
faulty parties: no party has received, echoed, voted for or delivered anything; if the leader is
not in `F`, it has sent its proposal `(init, input)` to every party, and otherwise nothing has
been sent. -/
def brachaStart (leader : P) (input : V) (F : Finset P) : BrachaState P V where
  sent := {x | leader ∉ F ∧ x.1 = leader ∧ x.2.2 = (.init, input)}
  rcvd _ := ∅
  echoed _ := none
  voted _ := none
  delivered _ := none

/-- **Fair executions of Bracha's broadcast.** A sequence $s_0, s_1, \dots$ of global states is
fair for a set $F$ of faulty parties when every message sent to a non-faulty party is
eventually received: if $(p, j, m)$ is among the messages sent in some $s_k$ and $j \notin F$,
then $(p, m)$ is among the messages $j$ has received in some $s_{k'}$. -/
def BrachaFair (F : Finset P) (ss : ωSequence (BrachaState P V)) : Prop :=
  ∀ k p j m, (p, j, m) ∈ (ss k).sent → j ∉ F → ∃ k', (p, m) ∈ (ss k').rcvd j

/-! ### Proofs -/

namespace Bracha

/-! ### The effect of a step -/

section Step

variable {f : ℕ} {leader : P} {F : Finset P}

/-- The vote threshold of party `i` for `v` in `s`. -/
private abbrev VoteReady (f : ℕ) (s : BrachaState P V) (i : P) (v : V) : Prop :=
  Fintype.card P - f ≤ #{p | (p, .echo, v) ∈ s.rcvd i} ∨ f + 1 ≤ #{p | (p, .vote, v) ∈ s.rcvd i}

/-- What a receiving step does, field by field. -/
private structure Step (f : ℕ) (leader : P) (F : Finset P) (s t : BrachaState P V) (q i : P)
    (k : BrachaKind) (v : V) : Prop where
  honest : i ∉ F
  src : q ∈ F ∨ (q, i, k, v) ∈ s.sent
  fresh : (q, k, v) ∉ s.rcvd i
  rcvd : ∀ j, t.rcvd j = if j = i then insert (q, k, v) (s.rcvd i) else s.rcvd j
  sent : ∀ p j m, (p, j, m) ∈ t.sent ↔ (p, j, m) ∈ s.sent ∨ p = i ∧
    (s.echoed i = none ∧ k = .init ∧ q = leader ∧ m = (.echo, v) ∨
      s.voted i = none ∧ VoteReady f t i v ∧ m = (.vote, v))
  echoed : ∀ j, t.echoed j =
    if j = i ∧ s.echoed i = none ∧ k = .init ∧ q = leader then some v else s.echoed j
  voted : ∀ j, t.voted j =
    if j = i ∧ s.voted i = none ∧ VoteReady f t i v then some v else s.voted j
  delivered : ∀ j, t.delivered j =
    if j = i ∧ s.delivered i = none ∧ Fintype.card P - f ≤ #{p | (p, .vote, v) ∈ t.rcvd i}
    then some v else s.delivered j

private lemma step_of_tr {s t : BrachaState P V} {q i : P} {k : BrachaKind} {v : V}
    (h : (brachaLTS f leader F).Tr s (some (q, i, k, v)) t) : Step f leader F s t q i k v := by
  obtain ⟨hi, hsrc, hnew, rfl⟩ := h
  refine ⟨hi, hsrc, hnew, fun j => ?_, fun p j m => ?_, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · by_cases hj : j = i <;> simp [hj]
  · simp [VoteReady]
  · by_cases hj : j = i <;> simp [hj]
  · by_cases hj : j = i <;> simp [hj, VoteReady]
  · by_cases hj : j = i <;> simp [hj]

end Step

/-! ### Monotonicity -/

section Mono

variable {f : ℕ} {leader : P} {F : Finset P}

/-- The parts of a state that steps only extend. -/
private structure Le (s t : BrachaState P V) : Prop where
  sent : s.sent ⊆ t.sent
  rcvd : ∀ i, s.rcvd i ⊆ t.rcvd i
  echoed : ∀ i v, s.echoed i = some v → t.echoed i = some v
  voted : ∀ i v, s.voted i = some v → t.voted i = some v
  delivered : ∀ i v, s.delivered i = some v → t.delivered i = some v

omit [Fintype P] [DecidableEq P] [DecidableEq V] in
private lemma Le.refl (s : BrachaState P V) : Le s s :=
  ⟨subset_rfl, fun _ => subset_rfl, fun _ _ => id, fun _ _ => id, fun _ _ => id⟩

omit [Fintype P] [DecidableEq P] [DecidableEq V] in
private lemma Le.trans {s t u : BrachaState P V} (h : Le s t) (h' : Le t u) : Le s u :=
  ⟨h.sent.trans h'.sent, fun i => (h.rcvd i).trans (h'.rcvd i),
    fun i v hv => h'.echoed i v (h.echoed i v hv), fun i v hv => h'.voted i v (h.voted i v hv),
    fun i v hv => h'.delivered i v (h.delivered i v hv)⟩

private lemma le_of_tr {s t : BrachaState P V} {a : Option (P × P × BrachaKind × V)}
    (h : (brachaLTS f leader F).Tr s a t) : Le s t := by
  rcases a with _ | ⟨q, i, k, v⟩
  · cases h
    exact Le.refl s
  have st := step_of_tr h
  refine ⟨fun x hx => ?_, fun j => ?_, fun j w hw => ?_, fun j w hw => ?_, fun j w hw => ?_⟩
  · obtain ⟨p, j, m⟩ := x
    exact (st.sent p j m).2 (Or.inl hx)
  · rw [st.rcvd]
    split_ifs with hj
    · subst hj
      exact subset_insert _ _
    · exact subset_rfl
  · rw [st.echoed]
    split_ifs with hc
    · obtain ⟨rfl, hn, -⟩ := hc
      simp [hn] at hw
    · exact hw
  · rw [st.voted]
    split_ifs with hc
    · obtain ⟨rfl, hn, -⟩ := hc
      simp [hn] at hw
    · exact hw
  · rw [st.delivered]
    split_ifs with hc
    · obtain ⟨rfl, hn, -⟩ := hc
      simp [hn] at hw
    · exact hw

private lemma le_of_exec {ss : ωSequence (BrachaState P V)}
    {μs : ωSequence (Option (P × P × BrachaKind × V))}
    (h : (brachaLTS f leader F).OmegaExecution ss μs) {a b : ℕ} (hab : a ≤ b) :
    Le (ss a) (ss b) := by
  induction hab with
  | refl => exact Le.refl _
  | step _ ih => exact ih.trans (le_of_tr (h _))

private lemma card_mono {r r' : Finset (P × BrachaKind × V)} (h : r ⊆ r') (m : BrachaKind × V) :
    #{p | (p, m) ∈ r} ≤ #{p | (p, m) ∈ r'} :=
  card_le_card fun p hp => by
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    exact h hp

private lemma card_insert_ne {r : Finset (P × BrachaKind × V)} {q : P} {k k' : BrachaKind} {v w : V}
    (hw : w ≠ v) : #{p | (p, k', w) ∈ insert (q, k, v) r} = #{p | (p, k', w) ∈ r} := by
  congr 1
  ext p
  simp [hw]

end Mono

/-! ### Counting -/

section Counting

variable {f : ℕ} {F : Finset P}

omit [Fintype P] [DecidableEq P] in
private lemma exists_honest_of_card {A : Finset P} (hF : #F ≤ f) (hA : f + 1 ≤ #A) :
    ∃ p ∈ A, p ∉ F :=
  exists_mem_notMem_of_card_lt_card (by omega)

omit [DecidableEq P] in
/-- Quorum intersection: two sets of `n - f` parties share a non-faulty party. -/
private lemma exists_honest_inter (hf : 3 * f < Fintype.card P) (hF : #F ≤ f) {A B : Finset P}
    (hA : Fintype.card P - f ≤ #A) (hB : Fintype.card P - f ≤ #B) :
    ∃ p ∈ A, p ∈ B ∧ p ∉ F := by
  classical
  have h₁ := card_union_add_card_inter A B
  have h₂ : #(A ∪ B) ≤ Fintype.card P := card_le_univ _
  obtain ⟨p, hp, hpF⟩ := exists_mem_notMem_of_card_lt_card (s := F) (t := A ∩ B) (by omega)
  exact ⟨p, (mem_inter.1 hp).1, (mem_inter.1 hp).2, hpF⟩

private lemma le_card_compl (hF : #F ≤ f) : Fintype.card P - f ≤ #Fᶜ := by
  rw [card_compl]
  omega

end Counting

/-! ### The invariant -/

section Invariant

variable {f : ℕ} {leader : P} {input : V} {F : Finset P}

/-- The inductive invariant of Bracha's broadcast. -/
private structure Inv (f : ℕ) (leader : P) (input : V) (F : Finset P) (s : BrachaState P V) :
    Prop where
  sent_src : ∀ {p j m}, (p, j, m) ∈ s.sent → p ∉ F
  sent_init : ∀ {p j w}, (p, j, .init, w) ∈ s.sent → p = leader ∧ w = input
  sent_echo : ∀ {p j w}, (p, j, .echo, w) ∈ s.sent → s.echoed p = some w
  sent_vote : ∀ {p j w}, (p, j, .vote, w) ∈ s.sent → s.voted p = some w
  echoed_sent : ∀ {p w}, s.echoed p = some w → ∀ j, (p, j, .echo, w) ∈ s.sent
  voted_sent : ∀ {p w}, s.voted p = some w → ∀ j, (p, j, .vote, w) ∈ s.sent
  leader_sent : leader ∉ F → ∀ j, (leader, j, .init, input) ∈ s.sent
  rcvd_sent : ∀ {i q m}, (q, m) ∈ s.rcvd i → q ∈ F ∨ (q, i, m) ∈ s.sent
  echoed_rcvd : ∀ {i w}, s.echoed i = some w → (leader, .init, w) ∈ s.rcvd i
  rcvd_echoed : ∀ {i w}, i ∉ F → (leader, .init, w) ∈ s.rcvd i → s.echoed i ≠ none
  voted_quorum : ∀ {i w}, s.voted i = some w →
    ∃ k, Fintype.card P - f ≤ #{p | (p, .echo, w) ∈ s.rcvd k}
  quorum_voted : ∀ {i w}, i ∉ F → VoteReady f s i w → s.voted i ≠ none
  delivered_quorum : ∀ {i w}, s.delivered i = some w →
    Fintype.card P - f ≤ #{p | (p, .vote, w) ∈ s.rcvd i}
  quorum_delivered : ∀ {i w}, i ∉ F → Fintype.card P - f ≤ #{p | (p, .vote, w) ∈ s.rcvd i} →
    s.delivered i ≠ none

private lemma inv_start (hf : 3 * f < Fintype.card P) :
    Inv f leader input F (brachaStart leader input F) where
  sent_src h := by simp_all [brachaStart]
  sent_init h := by simp_all [brachaStart]
  sent_echo h := by simp_all [brachaStart]
  sent_vote h := by simp_all [brachaStart]
  echoed_sent h := by simp_all [brachaStart]
  voted_sent h := by simp_all [brachaStart]
  leader_sent h j := by simp [brachaStart, h]
  rcvd_sent h := by simp_all [brachaStart]
  echoed_rcvd h := by simp_all [brachaStart]
  rcvd_echoed _ h := by simp_all [brachaStart]
  voted_quorum h := by simp_all [brachaStart]
  quorum_voted _ h := by simp [brachaStart, VoteReady] at h; omega
  delivered_quorum h := by simp_all [brachaStart]
  quorum_delivered _ h := by simp [brachaStart] at h; omega

private lemma inv_of_tr (hF : #F ≤ f) {s t : BrachaState P V} {a : Option (P × P × BrachaKind × V)}
    (hI : Inv f leader input F s) (h : (brachaLTS f leader F).Tr s a t) :
    Inv f leader input F t := by
  rcases a with _ | ⟨q, i, k, v⟩
  · cases h
    exact hI
  have st := step_of_tr h
  have L := le_of_tr h
  -- A message received from a non-faulty party was sent to the receiver.
  have rcvd_sent' : ∀ {j q' m}, (q', m) ∈ t.rcvd j → q' ∈ F ∨ (q', j, m) ∈ s.sent := by
    intro j q' m hm
    rw [st.rcvd] at hm
    split_ifs at hm with hj
    · subst hj
      rcases mem_insert.1 hm with hm | hm
      · simp only [Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        exact st.src
      · exact hI.rcvd_sent hm
    · exact hI.rcvd_sent hm
  refine ⟨fun {p j m} hx => ?_, fun {p j w} hx => ?_, fun {p j w} hx => ?_, fun {p j w} hx => ?_,
    fun {p w} hw j => ?_, fun {p w} hw j => ?_, fun hl j => L.sent (hI.leader_sent hl j),
    fun {j q' m} hm => (rcvd_sent' hm).imp_right fun h => L.sent h,
    fun {j w} hw => ?_, fun {j w} hj hm => ?_, fun {j w} hw => ?_, fun {j w} hj hr => ?_,
    fun {j w} hw => ?_, fun {j w} hj hr => ?_⟩
  · rcases (st.sent p j m).1 hx with hx | ⟨rfl, -⟩
    · exact hI.sent_src hx
    · exact st.honest
  · rcases (st.sent p j _).1 hx with hx | ⟨-, ⟨-, -, -, h⟩ | ⟨-, -, h⟩⟩
    · exact hI.sent_init hx
    · simp at h
    · simp at h
  · rcases (st.sent p j _).1 hx with hx | ⟨rfl, ⟨hn, hk, hq, h⟩ | ⟨-, -, h⟩⟩
    · exact L.echoed _ _ (hI.sent_echo hx)
    · simp only [Prod.mk.injEq, true_and] at h
      subst h
      rw [st.echoed, ite_eq_left ⟨rfl, hn, hk, hq⟩]
    · simp at h
  · rcases (st.sent p j _).1 hx with hx | ⟨rfl, ⟨-, -, -, h⟩ | ⟨hn, hr, h⟩⟩
    · exact L.voted _ _ (hI.sent_vote hx)
    · simp at h
    · simp only [Prod.mk.injEq, true_and] at h
      subst h
      rw [st.voted, ite_eq_left ⟨rfl, hn, hr⟩]
  · rw [st.echoed] at hw
    split_ifs at hw with hc
    · obtain ⟨rfl, hn, hk, hq⟩ := hc
      cases hw
      exact (st.sent _ _ _).2 (Or.inr ⟨rfl, Or.inl ⟨hn, hk, hq, rfl⟩⟩)
    · exact L.sent (hI.echoed_sent hw j)
  · rw [st.voted] at hw
    split_ifs at hw with hc
    · obtain ⟨rfl, hn, hr⟩ := hc
      cases hw
      exact (st.sent _ _ _).2 (Or.inr ⟨rfl, Or.inr ⟨hn, hr, rfl⟩⟩)
    · exact L.sent (hI.voted_sent hw j)
  · rw [st.echoed] at hw
    split_ifs at hw with hc
    · obtain ⟨rfl, -, rfl, rfl⟩ := hc
      cases hw
      rw [st.rcvd, ite_eq_left rfl]
      exact mem_insert_self _ _
    · exact L.rcvd _ (hI.echoed_rcvd hw)
  · rw [st.echoed]
    split_ifs with hc
    · simp
    · intro hnone
      rw [st.rcvd] at hm
      split_ifs at hm with hji
      · subst hji
        rcases mem_insert.1 hm with hm | hm
        · simp only [Prod.mk.injEq] at hm
          obtain ⟨rfl, rfl, rfl⟩ := hm
          exact hc ⟨rfl, hnone, rfl, rfl⟩
        · exact hI.rcvd_echoed hj hm hnone
      · exact hI.rcvd_echoed hj hm hnone
  · rw [st.voted] at hw
    split_ifs at hw with hc
    · obtain ⟨rfl, -, hr⟩ := hc
      cases hw
      rcases hr with hr | hr
      · exact ⟨j, hr⟩
      · obtain ⟨p, hp, hpF⟩ := exists_honest_of_card hF hr
        simp only [mem_filter, mem_univ, true_and] at hp
        rcases rcvd_sent' hp with hpF' | hp
        · exact absurd hpF' hpF
        obtain ⟨k', hq⟩ := hI.voted_quorum (hI.sent_vote hp)
        exact ⟨k', hq.trans (card_mono (L.rcvd k') _)⟩
    · obtain ⟨k', hq⟩ := hI.voted_quorum hw
      exact ⟨k', hq.trans (card_mono (L.rcvd k') _)⟩
  · rw [st.voted]
    split_ifs with hc
    · simp
    · intro hnone
      by_cases hji : j = i
      · subst hji
        by_cases hwv : w = v
        · subst hwv
          exact hc ⟨rfl, hnone, hr⟩
        · refine hI.quorum_voted (w := w) hj ?_ hnone
          unfold VoteReady at hr
          rwa [st.rcvd, ite_eq_left rfl, card_insert_ne hwv, card_insert_ne hwv] at hr
      · refine hI.quorum_voted (w := w) hj ?_ hnone
        simpa only [VoteReady, st.rcvd, ite_eq_right hji] using hr
  · rw [st.delivered] at hw
    split_ifs at hw with hc
    · obtain ⟨rfl, -, hr⟩ := hc
      cases hw
      exact hr
    · exact (hI.delivered_quorum hw).trans (card_mono (L.rcvd j) _)
  · rw [st.delivered]
    split_ifs with hc
    · simp
    · intro hnone
      by_cases hji : j = i
      · subst hji
        by_cases hwv : w = v
        · subst hwv
          exact hc ⟨rfl, hnone, hr⟩
        · refine hI.quorum_delivered (w := w) hj ?_ hnone
          rwa [st.rcvd, ite_eq_left rfl, card_insert_ne hwv] at hr
      · refine hI.quorum_delivered (w := w) hj ?_ hnone
        simpa only [st.rcvd, ite_eq_right hji] using hr

private lemma inv_of_reach (hf : 3 * f < Fintype.card P) (hF : #F ≤ f) {s : BrachaState P V}
    (h : (brachaLTS f leader F).CanReach (brachaStart leader input F) s) :
    Inv f leader input F s := by
  obtain ⟨μs, hμs⟩ := h
  exact LTS.mtrInv_of_trInv (fun _ _ _ htr hI => inv_of_tr hF hI htr) _ _ _ hμs (inv_start hf)

end Invariant

/-! ### Safety -/

section Safety

variable {f : ℕ} {leader : P} {input : V} {F : Finset P} {s : BrachaState P V}

/-- No two parties vote for different values. -/
private lemma Inv.voted_eq (hf : 3 * f < Fintype.card P) (hF : #F ≤ f)
    (hI : Inv f leader input F s) {i j : P} {v w : V} (hv : s.voted i = some v)
    (hw : s.voted j = some w) : v = w := by
  obtain ⟨k, hkv⟩ := hI.voted_quorum hv
  obtain ⟨k', hkw⟩ := hI.voted_quorum hw
  obtain ⟨p, hpv, hpw, hpF⟩ := exists_honest_inter hf hF hkv hkw
  simp only [mem_filter, mem_univ, true_and] at hpv hpw
  exact Option.some_injective _ <| (hI.sent_echo ((hI.rcvd_sent hpv).resolve_left hpF)).symm.trans
    (hI.sent_echo ((hI.rcvd_sent hpw).resolve_left hpF))

/-- A delivered value has been voted for by a non-faulty party. -/
private lemma Inv.voted_of_delivered (hf : 3 * f < Fintype.card P) (hF : #F ≤ f)
    (hI : Inv f leader input F s) {i : P} {v : V} (hv : s.delivered i = some v) :
    ∃ p ∉ F, s.voted p = some v := by
  have hq := hI.delivered_quorum hv
  obtain ⟨p, hp, hpF⟩ :=
    exists_honest_of_card (A := {p | (p, .vote, v) ∈ s.rcvd i}) hF (by omega)
  simp only [mem_filter, mem_univ, true_and] at hp
  exact ⟨p, hpF, hI.sent_vote ((hI.rcvd_sent hp).resolve_left hpF)⟩

/-- With a non-faulty leader, every echoed value is the leader's input. -/
private lemma Inv.echoed_eq_input (hI : Inv f leader input F s) (hl : leader ∉ F) {i : P} {w : V}
    (hw : s.echoed i = some w) : w = input :=
  (hI.sent_init ((hI.rcvd_sent (hI.echoed_rcvd hw)).resolve_left hl)).2

/-- With a non-faulty leader, every vote is for the leader's input. -/
private lemma Inv.voted_eq_input (hf : 3 * f < Fintype.card P) (hF : #F ≤ f)
    (hI : Inv f leader input F s) (hl : leader ∉ F) {i : P} {w : V} (hw : s.voted i = some w) :
    w = input := by
  obtain ⟨k, hk⟩ := hI.voted_quorum hw
  obtain ⟨p, hp, hpF⟩ :=
    exists_honest_of_card (A := {p | (p, .echo, w) ∈ s.rcvd k}) hF (by omega)
  simp only [mem_filter, mem_univ, true_and] at hp
  exact hI.echoed_eq_input hl (hI.sent_echo ((hI.rcvd_sent hp).resolve_left hpF))

end Safety

/-! ### Liveness -/

section Liveness

variable {f : ℕ} {leader : P} {input : V} {F : Finset P} {ss : ωSequence (BrachaState P V)}
  {μs : ωSequence (Option (P × P × BrachaKind × V))}

private lemma inv_of_exec (hf : 3 * f < Fintype.card P) (hF : #F ≤ f)
    (h : (brachaLTS f leader F).OmegaExecution ss μs) (h0 : ss 0 = brachaStart leader input F)
    (k : ℕ) :
    Inv f leader input F (ss k) :=
  inv_of_reach hf hF (h0 ▸ ⟨_, h.extract_mTr (Nat.zero_le k)⟩)

/-- In a fair execution, a non-faulty party eventually receives what each of a finite set of
parties sends it. -/
private lemma exists_rcvd_all (h : (brachaLTS f leader F).OmegaExecution ss μs)
    (hfair : BrachaFair F ss)
    {i : P} (hi : i ∉ F) (m : BrachaKind × V) (S : Finset P)
    (hS : ∀ p ∈ S, ∃ k, (p, i, m) ∈ (ss k).sent) : ∃ K, ∀ p ∈ S, (p, m) ∈ (ss K).rcvd i := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a S ha ih =>
    obtain ⟨K, hK⟩ := ih fun p hp => hS p (mem_insert_of_mem hp)
    obtain ⟨ka, hka⟩ := hS a (mem_insert_self a S)
    obtain ⟨K', hK'⟩ := hfair ka a i m hka hi
    refine ⟨max K K', fun p hp => ?_⟩
    rcases mem_insert.1 hp with rfl | hp
    · exact (le_of_exec h (le_max_right K K')).rcvd i hK'
    · exact (le_of_exec h (le_max_left K K')).rcvd i (hK p hp)

/-- If every non-faulty party eventually votes for `v`, every non-faulty party eventually
delivers. -/
private lemma exists_delivered (hf : 3 * f < Fintype.card P) (hF : #F ≤ f)
    (h : (brachaLTS f leader F).OmegaExecution ss μs) (h0 : ss 0 = brachaStart leader input F)
    (hfair : BrachaFair F ss) {v : V} (hv : ∀ p ∉ F, ∃ k, (ss k).voted p = some v) {i : P}
    (hi : i ∉ F) : ∃ k, (ss k).delivered i ≠ none := by
  have I := inv_of_exec hf hF h h0
  obtain ⟨K, hK⟩ := exists_rcvd_all h hfair hi (.vote, v) Fᶜ fun p hp => by
    obtain ⟨k, hk⟩ := hv p (mem_compl.1 hp)
    exact ⟨k, (I k).voted_sent hk i⟩
  exact ⟨K, (I K).quorum_delivered hi <| (le_card_compl hF).trans <|
    card_le_card fun p hp => by simpa using hK p hp⟩

private lemma validity (hf : 3 * f < Fintype.card P) (hF : #F ≤ f) (hl : leader ∉ F)
    (h : (brachaLTS f leader F).OmegaExecution ss μs) (h0 : ss 0 = brachaStart leader input F)
    (hfair : BrachaFair F ss) {i : P} (hi : i ∉ F) : ∃ k, (ss k).delivered i = some input := by
  have I := inv_of_exec hf hF h h0
  -- Every non-faulty party receives the leader's proposal and echoes it.
  have hecho : ∀ p ∉ F, ∃ k, (ss k).echoed p = some input := by
    intro p hp
    obtain ⟨k, hk⟩ := hfair 0 leader p (.init, input)
      (by rw [h0]; exact (inv_start hf).leader_sent hl p) hp
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 ((I k).rcvd_echoed hp hk)
    rw [(I k).echoed_eq_input hl hw] at hw
    exact ⟨k, hw⟩
  -- Every non-faulty party receives these `n - f` echoes and votes for the input.
  have hvote : ∀ p ∉ F, ∃ k, (ss k).voted p = some input := by
    intro p hp
    obtain ⟨K, hK⟩ := exists_rcvd_all h hfair hp (.echo, input) Fᶜ fun q hq => by
      obtain ⟨k, hk⟩ := hecho q (mem_compl.1 hq)
      exact ⟨k, (I k).echoed_sent hk p⟩
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 <| (I K).quorum_voted hp <| Or.inl <|
      (le_card_compl hF).trans <| card_le_card fun q hq => by simpa using hK q hq
    rw [(I K).voted_eq_input hf hF hl hw] at hw
    exact ⟨K, hw⟩
  obtain ⟨K, hK⟩ := exists_delivered hf hF h h0 hfair hvote hi
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hK
  obtain ⟨p, -, hp⟩ := (I K).voted_of_delivered hf hF hw
  rw [(I K).voted_eq_input hf hF hl hp] at hw
  exact ⟨K, hw⟩

private lemma totality (hf : 3 * f < Fintype.card P) (hF : #F ≤ f)
    (h : (brachaLTS f leader F).OmegaExecution ss μs) (h0 : ss 0 = brachaStart leader input F)
    (hfair : BrachaFair F ss) (hdel : ∃ i ∉ F, ∃ k v, (ss k).delivered i = some v) {j : P}
    (hj : j ∉ F) : ∃ k v, (ss k).delivered j = some v := by
  have I := inv_of_exec hf hF h h0
  obtain ⟨i, -, k₀, v, hv⟩ := hdel
  -- The non-faulty parties whose votes for `v` made `i` deliver.
  set G : Finset P := ({p | (p, .vote, v) ∈ (ss k₀).rcvd i} : Finset P) \ F with hGdef
  have hG : f + 1 ≤ #G := by
    have h₁ := (I k₀).delivered_quorum hv
    have h₂ : #{p | (p, BrachaKind.vote, v) ∈ (ss k₀).rcvd i} - #F ≤ #G := le_card_sdiff _ _
    omega
  have hGv : ∀ p ∈ G, (ss k₀).voted p = some v := by
    intro p hp
    simp only [hGdef, mem_sdiff, mem_filter, mem_univ, true_and] at hp
    exact (I k₀).sent_vote (((I k₀).rcvd_sent hp.1).resolve_left hp.2)
  obtain ⟨q, hq⟩ : G.Nonempty := card_pos.1 (by omega)
  -- Every non-faulty party receives these `f + 1` votes and votes for `v`.
  have hvote : ∀ p ∉ F, ∃ k, (ss k).voted p = some v := by
    intro p hp
    obtain ⟨K, hK⟩ := exists_rcvd_all h hfair hp (.vote, v) G fun q hq =>
      ⟨k₀, (I k₀).voted_sent (hGv q hq) p⟩
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 <| (I K).quorum_voted hp <| Or.inr <|
      hG.trans <| card_le_card fun q hq => by simpa using hK q hq
    have hwv := (I (max K k₀)).voted_eq hf hF ((le_of_exec h (le_max_left K k₀)).voted _ _ hw)
      ((le_of_exec h (le_max_right K k₀)).voted _ _ (hGv q hq))
    rw [hwv] at hw
    exact ⟨K, hw⟩
  obtain ⟨K, hK⟩ := exists_delivered hf hF h h0 hfair hvote hj
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hK
  exact ⟨K, w, hw⟩

end Liveness

end Bracha

open Bracha in
/-- **Bracha's Byzantine reliable broadcast.** Let $n$ parties run Bracha's protocol with a
given leader whose input is $v$, where a set $F$ of at most $f$ parties is faulty and
$n > 3f$. Consider the executions of the protocol's transition system from its initial state.
1. *Validity.* If the leader is not in $F$, then in every fair infinite execution every party
   outside $F$ delivers $v$ at some point.
2. *Agreement.* In every reachable state, any two parties outside $F$ that have delivered a value
   have delivered the same value.
3. *Totality.* In every fair infinite execution, if some party outside $F$ delivers a value at
   some point, then every party outside $F$ delivers a value at some point. -/
theorem bracha_reliable_broadcast (f : ℕ) (hf : 3 * f < Fintype.card P) (F : Finset P) (hF : #F ≤ f)
    (leader : P) (input : V) :
    (leader ∉ F → ∀ (ss : ωSequence (BrachaState P V))
      (μs : ωSequence (Option (P × P × BrachaKind × V))),
      (brachaLTS f leader F).OmegaExecution ss μs → ss 0 = brachaStart leader input F →
      BrachaFair F ss → ∀ i ∉ F, ∃ k, (ss k).delivered i = some input) ∧
    (∀ s, (brachaLTS f leader F).CanReach (brachaStart leader input F) s → ∀ i ∉ F, ∀ j ∉ F, ∀ v w,
      s.delivered i = some v → s.delivered j = some w → v = w) ∧
    (∀ (ss : ωSequence (BrachaState P V)) (μs : ωSequence (Option (P × P × BrachaKind × V))),
      (brachaLTS f leader F).OmegaExecution ss μs → ss 0 = brachaStart leader input F →
      BrachaFair F ss → (∃ i ∉ F, ∃ k v, (ss k).delivered i = some v) →
      ∀ j ∉ F, ∃ k v, (ss k).delivered j = some v) := by
  refine ⟨fun hl ss μs h h0 hfair i hi => validity hf hF hl h h0 hfair hi,
    fun s hs i _ j _ v w hv hw => ?_,
    fun ss μs h h0 hfair hdel j hj => totality hf hF h h0 hfair hdel hj⟩
  have I := inv_of_reach hf hF hs
  obtain ⟨p, -, hp⟩ := I.voted_of_delivered hf hF hv
  obtain ⟨p', -, hp'⟩ := I.voted_of_delivered hf hF hw
  exact I.voted_eq hf hF hp hp'

end Cslib.Distributed.Byzantine
