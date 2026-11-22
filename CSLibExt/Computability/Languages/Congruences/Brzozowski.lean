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

/-- The subset construction of the reversal: from a set of states, reading `a` moves to the
states whose `a`-successor lies in the set; it starts from the accepting states and accepts the
sets containing the start state. -/
def revDet : DFA α (Finset σ) where
  step S a := Finset.univ.filter fun q => M.step q a ∈ S
  start := Finset.univ.filter (· ∈ M.accept)
  accept := {S | M.start ∈ S}

instance decidableMemRevDetAccept : DecidablePred (· ∈ M.revDet.accept) := fun S =>
  inferInstanceAs (Decidable (M.start ∈ S))

/-- The subset reached on `w`: the states from which `w.reverse` is accepted. -/
theorem revDet_eval (w : List α) :
    M.revDet.eval w = Finset.univ.filter fun q => M.evalFrom q w.reverse ∈ M.accept := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
      rw [eval_append_singleton, ih, List.reverse_append, List.reverse_singleton]
      ext q
      simp only [revDet, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl

/-- **`revDet` accepts the reversal.** -/
theorem revDet_accepts : M.revDet.accepts = M.accepts.reverse := by
  ext w
  rw [mem_accepts, revDet_eval, Language.mem_reverse, mem_accepts]
  simp [revDet]
  rfl

/-- **Brzozowski's lemma.** If every state of `M` is reachable, two words reach the same subset
of `M.revDet` exactly when they have the same left quotient of the reversed language. -/
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

/-- The reachable subsets of the determinized reversal. The search runs at most
`2 ^ Fintype.card σ` rounds, the number of subsets, and stops as soon as nothing changes. -/
abbrev MidState : Type _ :=
  {S // S ∈ M.revDet.reachableWithin (2 ^ Fintype.card σ) ∅}

/-- The intermediate automaton: the reachable subsets of the determinized reversal. -/
abbrev brzozowskiMid : DFA α M.MidState :=
  M.revDet.accessiblePartWithin (2 ^ Fintype.card σ) Fintype.card_finset.le

/-- The states of Brzozowski's automaton. -/
abbrev BrzozowskiState : Type _ :=
  {S // S ∈ M.brzozowskiMid.revDet.reachableWithin (2 ^ Fintype.card M.MidState) ∅}

/-- **Brzozowski's automaton**: reverse, determinize, keep the reachable subsets, twice. -/
def brzozowski : DFA α M.BrzozowskiState :=
  M.brzozowskiMid.revDet.accessiblePartWithin (2 ^ Fintype.card M.MidState)
    Fintype.card_finset.le

/-- Every state of the intermediate automaton is reached. -/
theorem brzozowskiMid_surjective (p : M.MidState) : ∃ w, M.brzozowskiMid.eval w = p :=
  M.revDet.accessiblePartWithin_surjective Fintype.card_finset.le p

/-- Every state of Brzozowski's automaton is reached. -/
theorem brzozowski_surjective (p : M.BrzozowskiState) : ∃ w, M.brzozowski.eval w = p :=
  M.brzozowskiMid.revDet.accessiblePartWithin_surjective Fintype.card_finset.le p

theorem brzozowskiMid_accepts : M.brzozowskiMid.accepts = M.accepts.reverse := by
  rw [brzozowskiMid, accessiblePartWithin_accepts, revDet_accepts]

/-- **Brzozowski's automaton accepts the language of `M`.** -/
theorem brzozowski_accepts : M.brzozowski.accepts = M.accepts := by
  rw [brzozowski, accessiblePartWithin_accepts, revDet_accepts, brzozowskiMid_accepts,
    Language.reverse_reverse]

/-- Two words reach the same state of Brzozowski's automaton exactly when they are Nerode
equivalent for the language of `M`. -/
theorem brzozowski_eval_eq_iff {w w' : List α} :
    M.brzozowski.eval w = M.brzozowski.eval w' ↔ nerodeRel M.accepts w w' := by
  rw [brzozowski, accessiblePartWithin_eval_eq_iff,
    revDet_eval_eq_iff M.brzozowskiMid M.brzozowskiMid_surjective, brzozowskiMid_accepts,
    Language.reverse_reverse]
  rfl

/-- The continuation language of a state of Brzozowski's automaton, through a word reaching it. -/
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

/-- The states of Brzozowski's automaton correspond to the continuation languages. -/
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

/-- **Brzozowski's automaton is the minimal automaton.** Renaming its states to the continuation
languages they determine gives exactly `Cslib.Language.minimizedDFA M`. -/
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
