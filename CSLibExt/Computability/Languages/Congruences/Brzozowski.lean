/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Brzozowski's minimization algorithm
-/
module

public import CSLibExt.Computability.Decidability.Regular
public import CSLibExt.Computability.Languages.Congruences.Minimization

/-!
# Brzozowski's minimization algorithm

J. A. Brzozowski, *Canonical regular expressions and minimal state graphs for definite events*,
Mathematical Theory of Automata, 1962: reversing a DFA, determinizing by the subset construction
and keeping the reachable subsets, twice, gives the minimal DFA. For a Mathlib `DFA` over a
finite alphabet with finitely many states every step is executable here.

## Main definitions

* `DFA.revDet M`: the subset construction of the reversal of `M`; the subset reached on `w` is
  the set of states from which `w.reverse` is accepted (`DFA.revDet_eval`).
* `DFA.brzozowski M`: reverse and determinize, keep the reachable subsets, twice. The reachable
  subsets are found by `DFA.accessiblePartWithin` (in `Decidability/Regular.lean`), a search
  that stops as soon as a round adds nothing, so the number of rounds is bounded by the number of
  reachable subsets rather than the number of all subsets. The state types are subtypes of the
  computed finsets, so their `Fintype` instance (`Finset.Subtype.fintype`) lists only those.

## Main results

* `DFA.revDet_accepts`: `M.revDet` accepts the reversal of the language of `M`.
* `DFA.revDet_eval_eq_iff`: **Brzozowski's lemma**. If every state of `M` is reachable, two
  words reach the same subset of `M.revDet` exactly when they have the same left quotient of the
  reversed language: the reachable part of `M.revDet` is the minimal DFA of the reversal.
* `DFA.brzozowski_accepts`, `DFA.brzozowski_eval_eq_iff`: the result accepts the language of `M`,
  and two words reach the same state exactly when they are Nerode equivalent.
* `DFA.reindex_brzozowski`: renaming its states along `DFA.brzozowskiEquiv` gives exactly
  `Cslib.Language.minimizedDFA M`, the semantic minimal automaton of
  `Congruences/Minimization.lean`.
-/

@[expose] public section

namespace DFA

open Cslib.Language

variable {α σ : Type*}

/-! ## Determinized reversal -/

section RevDet

variable [Fintype σ] [DecidableEq σ] (M : DFA α σ) [DecidablePred (· ∈ M.accept)]

/-- **Determinized reversal of a DFA.** For a DFA $M$ with finitely many states, the determinized
reversal of $M$ is the subset construction applied to the reversal of $M$: its states are the sets
of states of $M$; reading a letter $a$ from a set $S$ leads to the set of states $q$ whose
$a$-successor in $M$ lies in $S$; its start state is the set of accepting states of $M$; and it
accepts exactly the sets that contain the start state of $M$. -/
def revDet : DFA α (Finset σ) where
  step S a := Finset.univ.filter fun q => M.step q a ∈ S
  start := Finset.univ.filter (· ∈ M.accept)
  accept := {S | M.start ∈ S}

instance decidableMemRevDetAccept : DecidablePred (· ∈ M.revDet.accept) := fun S =>
  inferInstanceAs (Decidable (M.start ∈ S))

/-- **States reached in the determinized reversal.** Let $M$ be a DFA with finitely many states
and $w$ a word. On input $w$, the determinized reversal of $M$ reaches the set of states $q$ of
$M$ from which $M$, reading $w$ backwards starting at $q$, ends in an accepting state. -/
theorem revDet_eval (w : List α) :
    M.revDet.eval w = Finset.univ.filter fun q => M.evalFrom q w.reverse ∈ M.accept := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
      rw [eval_append_singleton, ih, List.reverse_append, List.reverse_singleton]
      ext q
      simp only [revDet, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl

/-- **The determinized reversal accepts the reversed language.** Let $M$ be a DFA with finitely
many states and $L$ its language, and write $w^R$ for the word $w$ read backwards. The
determinized reversal of $M$ accepts exactly the reversed language $L^R = \{w \mid w^R \in L\}$. -/
theorem revDet_accepts : M.revDet.accepts = M.accepts.reverse := by
  ext w
  rw [mem_accepts, revDet_eval, Language.mem_reverse, mem_accepts]
  simp [revDet]
  rfl

/-- **Brzozowski's lemma.** Let $M$ be a DFA with finitely many states in which every state is
reached from the start state by some word, and let $L$ be its language. Write $u^R$ for the word
$u$ read backwards, $L^R = \{u \mid u^R \in L\}$ for the reversed language, and
$w^{-1}K = \{v \mid wv \in K\}$ for the left quotient of a language $K$ by a word $w$. Then two
words $w$ and $w'$ lead the determinized reversal of $M$ from its start state to the same set of
states if and only if $w^{-1}L^R = w'^{-1}L^R$. -/
theorem revDet_eval_eq_iff (hacc : ∀ q, ∃ u, M.eval u = q) {w w' : List α} :
    M.revDet.eval w = M.revDet.eval w' ↔
      M.accepts.reverse.leftQuotient w = M.accepts.reverse.leftQuotient w' := by
  rw [revDet_eval, revDet_eval]
  have key : ∀ (x : List α) (v : List α), v ∈ M.accepts.reverse.leftQuotient x ↔
      M.evalFrom (M.eval v.reverse) x.reverse ∈ M.accept := by
    intro x v
    rw [Language.mem_leftQuotient, Language.mem_reverse, List.reverse_append, mem_accepts,
      eval, evalFrom_of_append]
  constructor
  · intro h
    ext v
    rw [key, key]
    have := congrArg (fun S => M.eval v.reverse ∈ S) h
    simpa using this
  · intro h
    ext q
    obtain ⟨u, rfl⟩ := hacc q
    have := congrArg (fun L => u.reverse ∈ L) h
    simp only [key, List.reverse_reverse] at this
    simpa using this

end RevDet

/-! ## Brzozowski's algorithm -/

section Brzozowski

variable [Fintype α] [Fintype σ] [DecidableEq σ] (M : DFA α σ) [DecidablePred (· ∈ M.accept)]

/-- **States of the intermediate Brzozowski automaton.** For a deterministic finite automaton $M$
over a finite alphabet with finite state set $Q$, the subsets of $Q$ reachable from the start state
in the subset construction of the reversal of $M$.

They are found by a reachability search of at most $2^{|Q|}$ rounds, the number of subsets, which
stops as soon as a round adds nothing. -/
abbrev MidState : Type _ :=
  {S // S ∈ M.revDet.reachableWithin (2 ^ Fintype.card σ) ∅}

/-- **The intermediate Brzozowski automaton.** For a deterministic finite automaton $M$ over a
finite alphabet with finitely many states, the subset construction of the reversal of $M$,
restricted to the subsets reachable from its start state. -/
abbrev brzozowskiMid : DFA α M.MidState :=
  M.revDet.accessiblePartWithin (2 ^ Fintype.card σ) Fintype.card_finset.le

/-- **States of Brzozowski's automaton.** For a deterministic finite automaton $M$ over a finite
alphabet with finitely many states, the subsets of states of the intermediate Brzozowski automaton
of $M$ that are reachable from the start state in the subset construction of its reversal. -/
abbrev BrzozowskiState : Type _ :=
  {S // S ∈ M.brzozowskiMid.revDet.reachableWithin (2 ^ Fintype.card M.MidState) ∅}

/-- **Brzozowski's automaton.** For a deterministic finite automaton $M$ over a finite alphabet
with finitely many states, the subset construction of the reversal of the intermediate Brzozowski
automaton of $M$, restricted to the subsets reachable from its start state. Equivalently: reverse,
determinize by the subset construction and keep the reachable subsets, twice. -/
def brzozowski : DFA α M.BrzozowskiState :=
  M.brzozowskiMid.revDet.accessiblePartWithin (2 ^ Fintype.card M.MidState)
    Fintype.card_finset.le

/-- **Every state of the intermediate Brzozowski automaton is reachable.** For a deterministic
finite automaton $M$ over a finite alphabet with finitely many states, every state of the
intermediate Brzozowski automaton of $M$ (the subset construction of the reversal of $M$
restricted to its reachable subsets) is reached from its start state by some word. -/
theorem brzozowskiMid_surjective (p : M.MidState) : ∃ w, M.brzozowskiMid.eval w = p :=
  M.revDet.accessiblePartWithin_surjective Fintype.card_finset.le p

/-- **Every state of Brzozowski's automaton is reachable.** For a deterministic finite automaton
$M$ over a finite alphabet with finitely many states, every state of Brzozowski's automaton of $M$
is reached from its start state by some word. -/
theorem brzozowski_surjective (p : M.BrzozowskiState) : ∃ w, M.brzozowski.eval w = p :=
  M.brzozowskiMid.revDet.accessiblePartWithin_surjective Fintype.card_finset.le p

theorem brzozowskiMid_accepts : M.brzozowskiMid.accepts = M.accepts.reverse := by
  rw [brzozowskiMid, accessiblePartWithin_accepts, revDet_accepts]

/-- **Brzozowski's automaton accepts the language of the original automaton.** For a deterministic
finite automaton $M$ over a finite alphabet with finitely many states, Brzozowski's automaton of
$M$ accepts exactly the language of $M$. -/
theorem brzozowski_accepts : M.brzozowski.accepts = M.accepts := by
  rw [brzozowski, accessiblePartWithin_accepts, revDet_accepts, brzozowskiMid_accepts,
    Language.reverse_reverse]

/-- **Brzozowski's automaton identifies exactly the Nerode equivalent words.** For a deterministic
finite automaton $M$ over a finite alphabet with finitely many states and words $w$ and $w'$,
Brzozowski's automaton of $M$ reaches the same state on $w$ as on $w'$ if and only if $w$ and $w'$
are Nerode equivalent for the language of $M$, that is, have the same left quotient. -/
theorem brzozowski_eval_eq_iff {w w' : List α} :
    M.brzozowski.eval w = M.brzozowski.eval w' ↔ nerodeRel M.accepts w w' := by
  rw [brzozowski, accessiblePartWithin_eval_eq_iff,
    revDet_eval_eq_iff M.brzozowskiMid M.brzozowskiMid_surjective, brzozowskiMid_accepts,
    Language.reverse_reverse]
  rfl

/-- **Residual language of a state of Brzozowski's automaton.** For a deterministic finite
automaton $M$ over a finite alphabet with finitely many states, the map that sends a state $p$ of
Brzozowski's automaton of $M$ to the language accepted by $M$ from the state that $M$ reaches on
$w$, where $w$ is a chosen word leading Brzozowski's automaton from its start state to $p$; this
language is one of the residual languages of the reachable states of $M$. -/
noncomputable def brzozowskiResidual (p : M.BrzozowskiState) : reachableResiduals M :=
  minimizedState M (M.brzozowski_surjective p).choose

theorem brzozowskiResidual_eval (w : List α) :
    M.brzozowskiResidual (M.brzozowski.eval w) = minimizedState M w := by
  have h := (M.brzozowski_surjective (M.brzozowski.eval w)).choose_spec
  rw [brzozowskiResidual, minimizedState_eq_iff_nerodeRel, ← brzozowski_eval_eq_iff]
  exact h

theorem brzozowskiResidual_bijective : Function.Bijective M.brzozowskiResidual := by
  constructor
  · intro p q hpq
    obtain ⟨w, rfl⟩ := M.brzozowski_surjective p
    obtain ⟨w', rfl⟩ := M.brzozowski_surjective q
    change M.brzozowskiResidual (M.brzozowski.eval w) =
      M.brzozowskiResidual (M.brzozowski.eval w') at hpq
    rw [brzozowskiResidual_eval, brzozowskiResidual_eval, minimizedState_eq_iff_nerodeRel,
      ← brzozowski_eval_eq_iff] at hpq
    exact hpq
  · rintro ⟨L, x, rfl⟩
    exact ⟨M.brzozowski.eval x, (M.brzozowskiResidual_eval x).trans rfl⟩

/-- **States of Brzozowski's automaton as residual languages.** For a deterministic finite
automaton $M$ over a finite alphabet with finitely many states, the bijection from the states of
Brzozowski's automaton of $M$ to the residual languages of the reachable states of $M$ that sends
each state $p$ to the language accepted by $M$ from the state that $M$ reaches on $w$, where $w$
is a chosen word leading Brzozowski's automaton from its start state to $p$. -/
noncomputable def brzozowskiEquiv : M.BrzozowskiState ≃ reachableResiduals M :=
  Equiv.ofBijective _ M.brzozowskiResidual_bijective

omit [Fintype α] in
private theorem dfa_ext {τ : Type*} {A B : DFA α τ} (h₁ : A.step = B.step) (h₂ : A.start = B.start)
    (h₃ : A.accept = B.accept) : A = B := by
  cases A
  cases B
  cases h₁
  cases h₂
  cases h₃
  rfl

/-- **Brzozowski's automaton is the minimal automaton.** Let $M$ be a DFA over a finite alphabet
with finitely many states, and let $L$ be its language. For a language $K$ and a word $w$, write
$w^{-1}K = \{v \mid wv \in K\}$ for the left quotient of $K$ by $w$. Every state of Brzozowski's
automaton of $M$ is reached by some word $w$; rename that state to $w^{-1}L$, which does not
depend on the choice of $w$. The renamed automaton is exactly the minimized DFA of $M$: its states
are the left quotients of $L$ by words, its start state is $L$, reading a letter $a$ (a word of
length one) sends $K$ to $a^{-1}K$, and it accepts the $K$ that contain the empty word. -/
theorem reindex_brzozowski : DFA.reindex M.brzozowskiEquiv M.brzozowski = minimizedDFA M := by
  have hsurj : ∀ q : reachableResiduals M, ∃ w, M.brzozowskiEquiv (M.brzozowski.eval w) = q :=
    fun q => by
      obtain ⟨p, rfl⟩ := M.brzozowskiEquiv.surjective q
      obtain ⟨w, rfl⟩ := M.brzozowski_surjective p
      exact ⟨w, rfl⟩
  have he : ∀ w, M.brzozowskiEquiv (M.brzozowski.eval w) = minimizedState M w :=
    M.brzozowskiResidual_eval
  refine dfa_ext ?_ ?_ ?_
  · funext q a
    obtain ⟨w, rfl⟩ := hsurj q
    change M.brzozowskiEquiv
      (M.brzozowski.step (M.brzozowskiEquiv.symm (M.brzozowskiEquiv (M.brzozowski.eval w))) a) = _
    rw [Equiv.symm_apply_apply, ← eval_append_singleton, he, he,
      minimizedDFA_step_minimizedState]
  · change M.brzozowskiEquiv (M.brzozowski.eval []) = _
    rw [he, ← minimizedDFA_eval]
    rfl
  · ext q
    obtain ⟨w, rfl⟩ := hsurj q
    change M.brzozowskiEquiv.symm (M.brzozowskiEquiv (M.brzozowski.eval w)) ∈
      M.brzozowski.accept ↔ _
    rw [Equiv.symm_apply_apply, he, ← minimizedDFA_eval]
    change w ∈ M.brzozowski.accepts ↔ w ∈ (minimizedDFA M).accepts
    rw [brzozowski_accepts, minimizedDFA_accepts]

end Brzozowski

end DFA
