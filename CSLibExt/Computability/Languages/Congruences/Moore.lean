/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Moore's minimization algorithm
-/
module

public import CSLibExt.Computability.Decidability.Regular
public import CSLibExt.Computability.Languages.Congruences.Minimization

/-!
# Moore's minimization algorithm

E. F. Moore, *Gedanken-experiments on sequential machines*, Automata Studies, 1956. For a
Mathlib `DFA` over a finite alphabet with finitely many states, Moore's algorithm computes state
equivalence by refinement: start from all pairs of states, keep a pair when its states agree on
acceptance and its successors on every letter are kept, and repeat until nothing changes. The
minimal automaton has the classes of reachable states as states.

## Main definitions

* `DFA.mooreStep`, `DFA.mooreRel`: one refinement round and its greatest fixed point, computed by
  iterating from all pairs until a round changes nothing (`DFA.mooreIter`).
* `DFA.MooreState M`: the classes of the reachable states (`DFA.reachable`) under `mooreRel`, a
  finite type with decidable equality.
* `DFA.mooreDFA M`: the quotient automaton.

## Main results

* `DFA.mem_mooreRel_iff`: two states are related exactly when they accept the same continuation
  languages (`Cslib.Language.StateEquivalent`).
* `DFA.mooreDFA_accepts`: the quotient accepts the language of `M`.
* `DFA.reindex_mooreDFA`: renaming the classes along `DFA.mooreEquiv` gives exactly
  `Cslib.Language.minimizedDFA M`, the semantic minimal automaton of
  `Congruences/Minimization.lean`.
* `DFA.card_mooreState`: the quotient has one state per Nerode class of the language.
-/

@[expose] public section

namespace DFA

variable {α σ : Type*} [Fintype α] [Fintype σ] [DecidableEq σ] (M : DFA α σ)
  [DecidablePred (· ∈ M.accept)]

/-! ## State equivalence by refinement -/

/-- **Moore refinement step.** Let $M$ be a DFA with state set $S$ and transition function
$\delta$. One round of Moore's refinement sends a set $E \subseteq S \times S$ of pairs of
states to the set of pairs $(p, q) \in S \times S$ such that $p$ is accepting if and only if
$q$ is accepting and, for every letter $a$, the pair $(\delta(p, a), \delta(q, a))$ lies in
$E$. -/
def mooreStep (E : Finset (σ × σ)) : Finset (σ × σ) :=
  Finset.univ.filter fun p =>
    (p.1 ∈ M.accept ↔ p.2 ∈ M.accept) ∧ ∀ a, (M.step p.1 a, M.step p.2 a) ∈ E

theorem mooreStep_mono : Monotone M.mooreStep := fun E F h p hp => by
  simp only [mooreStep, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact ⟨hp.1, fun a => h (hp.2 a)⟩

/-- **Stopping Moore iteration.** Let $M$ be a DFA over a finite alphabet with finitely many
states, and write $R$ for one round of Moore's refinement. For a set $E$ of pairs of states of
$M$ and a budget $n \in \mathbb{N}$, the stopping Moore iteration is defined by recursion on $n$:
with budget $0$ it returns $E$; with budget $n + 1$ it returns $E$ if $R(E) = E$, and otherwise
the stopping Moore iteration from $R(E)$ with budget $n$. -/
def mooreIter : ℕ → Finset (σ × σ) → Finset (σ × σ)
  | 0, E => E
  | n + 1, E =>
      let next := M.mooreStep E
      if next = E then E else mooreIter n next

/-- **Output of the stopping Moore iteration.** Let $M$ be a DFA over a finite alphabet with
finitely many states, and write $R$ for one round of Moore's refinement. For every
$n \in \mathbb{N}$ and every set $E$ of pairs of states of $M$, there is $k \le n$ such that the
stopping Moore iteration from $E$ with budget $n$ returns $R^k(E)$, and if $k < n$ then $R^k(E)$
is a fixed point of $R$, that is, $R(R^k(E)) = R^k(E)$. -/
theorem mooreIter_spec :
    ∀ (n : ℕ) (E : Finset (σ × σ)), ∃ k ≤ n, M.mooreIter n E = M.mooreStep^[k] E ∧
      (k < n → M.mooreStep (M.mooreStep^[k] E) = M.mooreStep^[k] E)
  | 0, E => ⟨0, le_rfl, rfl, fun h => absurd h (Nat.lt_irrefl 0)⟩
  | n + 1, E => by
      by_cases h : M.mooreStep E = E
      · exact ⟨0, Nat.zero_le _, by simp [mooreIter, h], fun _ => h⟩
      · obtain ⟨k, hk, heq, hfix⟩ := mooreIter_spec n (M.mooreStep E)
        refine ⟨k + 1, by omega, ?_, fun hlt => ?_⟩
        · simp only [mooreIter, h, ↓reduceIte, heq, Function.iterate_succ_apply]
        · rw [Function.iterate_succ_apply]
          exact hfix (by omega)

/-- **Moore's relation.** For a DFA $M$ over a finite alphabet with finite set of states $Q$,
Moore's relation is the set of pairs of states obtained from $Q \times Q$ by repeating rounds of
Moore's refinement until a round changes nothing, for at most $|Q \times Q|$ rounds. -/
def mooreRel : Finset (σ × σ) :=
  M.mooreIter (Fintype.card (σ × σ)) Finset.univ

theorem mooreStep_mooreRel : M.mooreStep M.mooreRel = M.mooreRel := by
  obtain ⟨k, hk, heq, hfix⟩ := M.mooreIter_spec (Fintype.card (σ × σ)) Finset.univ
  rw [mooreRel, heq]
  rcases Nat.lt_or_ge k (Fintype.card (σ × σ)) with hlt | hge
  · exact hfix hlt
  · obtain rfl : k = Fintype.card (σ × σ) := le_antisymm hk hge
    exact Finset.gfpFin_fixed M.mooreStep_mono

/-- **Moore's relation contains every post-fixed point.** Let $M$ be a DFA. If a set $Z$ of
pairs of states of $M$ is contained in its image under one round of Moore's refinement, then
$Z$ is contained in Moore's relation of $M$. -/
theorem subset_mooreRel {Z : Finset (σ × σ)} (hZ : Z ⊆ M.mooreStep Z) : Z ⊆ M.mooreRel := by
  obtain ⟨k, -, heq, -⟩ := M.mooreIter_spec (Fintype.card (σ × σ)) Finset.univ
  rw [mooreRel, heq]
  clear heq
  induction k with
  | zero => exact Finset.subset_univ _
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hZ.trans (M.mooreStep_mono ih)

theorem mem_mooreRel_unfold {p q : σ} :
    (p, q) ∈ M.mooreRel ↔
      (p ∈ M.accept ↔ q ∈ M.accept) ∧ ∀ a, (M.step p a, M.step q a) ∈ M.mooreRel := by
  conv_lhs => rw [← M.mooreStep_mooreRel]
  simp [mooreStep]

/-- **Correctness of Moore's refinement.** For a DFA $M$ over a finite alphabet with finitely
many states, two states $p$ and $q$ of $M$ are related by Moore's relation if and only if they
have the same continuation language: for every word $w$, $M$ started at $p$ accepts $w$ exactly
when $M$ started at $q$ accepts $w$. -/
theorem mem_mooreRel_iff {p q : σ} :
    (p, q) ∈ M.mooreRel ↔ M.acceptsFrom p = M.acceptsFrom q := by
  classical
  constructor
  · intro h
    have key : ∀ (z : List α) (p q : σ), (p, q) ∈ M.mooreRel →
        (M.evalFrom p z ∈ M.accept ↔ M.evalFrom q z ∈ M.accept) := by
      intro z
      induction z with
      | nil => exact fun p q h => ((M.mem_mooreRel_unfold).1 h).1
      | cons a z ih =>
          intro p q h
          rw [evalFrom_cons, evalFrom_cons]
          exact ih _ _ (((M.mem_mooreRel_unfold).1 h).2 a)
    ext z
    exact key z p q h
  · intro h
    have hle : (Finset.univ.filter fun pq : σ × σ => M.acceptsFrom pq.1 = M.acceptsFrom pq.2) ⊆
        M.mooreRel := by
      refine M.subset_mooreRel fun pq hpq => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mooreStep] at hpq ⊢
      refine ⟨?_, fun a => ?_⟩
      · have h : [] ∈ M.acceptsFrom pq.1 ↔ [] ∈ M.acceptsFrom pq.2 := by rw [hpq]
        rwa [mem_acceptsFrom, mem_acceptsFrom, evalFrom_nil, evalFrom_nil] at h
      · ext z
        have h : a :: z ∈ M.acceptsFrom pq.1 ↔ a :: z ∈ M.acceptsFrom pq.2 := by rw [hpq]
        rw [mem_acceptsFrom, mem_acceptsFrom, evalFrom_cons, evalFrom_cons] at h
        rw [mem_acceptsFrom, mem_acceptsFrom]
        exact h
    exact hle (by simp [h])

/-! ## The quotient automaton -/

/-- **Moore equivalence on reachable states.** For a DFA $M$, two reachable states $p$ and $q$
of $M$ are related when the pair $(p, q)$ lies in Moore's relation of $M$; this relation is an
equivalence relation on the reachable states of $M$. -/
def mooreSetoid : Setoid {s // s ∈ M.reachable} where
  r p q := (p.1, q.1) ∈ M.mooreRel
  iseqv :=
    ⟨fun _ => M.mem_mooreRel_iff.2 rfl,
      fun h => M.mem_mooreRel_iff.2 (M.mem_mooreRel_iff.1 h).symm,
      fun h₁ h₂ => M.mem_mooreRel_iff.2 ((M.mem_mooreRel_iff.1 h₁).trans (M.mem_mooreRel_iff.1 h₂))⟩

instance decidableMooreSetoidRel (p q : {s // s ∈ M.reachable}) :
    Decidable (@HasEquiv.Equiv _ (@instHasEquivOfSetoid _ M.mooreSetoid) p q) :=
  inferInstanceAs (Decidable ((p.1, q.1) ∈ M.mooreRel))

/-- **States of Moore's automaton.** For a DFA $M$, these are the equivalence classes of the
reachable states of $M$ under Moore equivalence, that is, under Moore's relation of $M$
restricted to reachable states. They are the states of Moore's minimal automaton. -/
def MooreState : Type _ :=
  Quotient M.mooreSetoid

instance : DecidableEq M.MooreState :=
  @Quotient.decidableEq _ M.mooreSetoid (M.decidableMooreSetoidRel)

instance : Fintype M.MooreState :=
  @Quotient.fintype _ _ M.mooreSetoid (M.decidableMooreSetoidRel)

/-- **Moore class of a reachable state.** Let $M$ be a DFA over a finite alphabet with finitely
many states. For a reachable state $s$ of $M$, its Moore class is the equivalence class of $s$
among the reachable states of $M$ under Moore's relation; it is a state of Moore's minimal
automaton of $M$. -/
def mooreClass (s : {s // s ∈ M.reachable}) : M.MooreState :=
  Quotient.mk M.mooreSetoid s

theorem mooreClass_eq_iff {p q : {s // s ∈ M.reachable}} :
    M.mooreClass p = M.mooreClass q ↔ M.acceptsFrom p.1 = M.acceptsFrom q.1 :=
  Quotient.eq.trans M.mem_mooreRel_iff

/-- **Moore's minimal automaton.** For a DFA $M$ over a finite alphabet with finitely many states,
Moore's minimal automaton of $M$ has as states the classes of reachable states of $M$ under
Moore's relation. Its start state is the class of the start state of $M$; reading a letter $a$
sends the class of a reachable state $s$ to the class of the state that $M$ reaches from $s$ on
$a$; and the class of $s$ is accepting exactly when $s$ is an accepting state of $M$.

These do not depend on the chosen member $s$, because Moore-related states agree on acceptance
and their successors on each letter are again Moore-related. -/
def mooreDFA : DFA α M.MooreState where
  step c a := Quotient.lift (fun p => M.mooreClass ⟨M.step p.1 a, M.step_mem_reachable p.2 a⟩)
    (fun _ _ h => (M.mooreClass_eq_iff).2
      (M.mem_mooreRel_iff.1 (((M.mem_mooreRel_unfold).1 h).2 a))) c
  start := M.mooreClass ⟨M.start, M.start_mem_reachable⟩
  accept := {c | Quotient.lift (fun p : {s // s ∈ M.reachable} => decide (p.1 ∈ M.accept))
    (fun _ _ h => decide_eq_decide.2 ((M.mem_mooreRel_unfold).1 h).1) c = true}

instance decidableMemMooreAccept : DecidablePred (· ∈ M.mooreDFA.accept) := fun c =>
  inferInstanceAs (Decidable (Quotient.lift (fun p : {s // s ∈ M.reachable} =>
    decide (p.1 ∈ M.accept)) _ c = true))

@[simp]
theorem mooreDFA_step_mooreClass (p : {s // s ∈ M.reachable}) (a : α) :
    M.mooreDFA.step (M.mooreClass p) a =
      M.mooreClass ⟨M.step p.1 a, M.step_mem_reachable p.2 a⟩ :=
  rfl

theorem mooreClass_mem_accept {p : {s // s ∈ M.reachable}} :
    M.mooreClass p ∈ M.mooreDFA.accept ↔ p.1 ∈ M.accept := by
  change decide (p.1 ∈ M.accept) = true ↔ _
  exact decide_eq_true_iff

theorem mooreDFA_eval (w : List α) :
    M.mooreDFA.eval w = M.mooreClass ⟨M.eval w, M.mem_reachable_iff.2 ⟨w, rfl⟩⟩ := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
      rw [eval_append_singleton, ih, mooreDFA_step_mooreClass]
      congr 2
      exact (M.eval_append_singleton w a).symm

/-- **Moore's automaton accepts the same language.** For a DFA $M$ over a finite alphabet with
finitely many states, Moore's minimal automaton of $M$ accepts exactly the language accepted by
$M$. -/
theorem mooreDFA_accepts : M.mooreDFA.accepts = M.accepts := by
  ext w
  rw [mem_accepts, mooreDFA_eval, mooreClass_mem_accept, mem_accepts]

/-! ## Agreement with the semantic minimal automaton -/

open Cslib.Language

/-- **Continuation language of a Moore class.** Let $M$ be a DFA over a finite alphabet with
finitely many states. Each state of Moore's minimal automaton of $M$, a class of reachable states
of $M$, is sent to the continuation language of any member $s$, the set of words that $M$
accepts when started at $s$; this is a reachable residual language of $M$. It does not depend on
the choice of $s$, because Moore-related states have the same continuation language. -/
def mooreResidual (c : M.MooreState) : reachableResiduals M :=
  Quotient.lift (fun p : {s // s ∈ M.reachable} => (⟨M.acceptsFrom p.1, by
      obtain ⟨w, hw⟩ := M.mem_reachable_iff.1 p.2
      exact ⟨w, by simp [hw]⟩⟩ : reachableResiduals M))
    (fun _ _ h => Subtype.ext (M.mem_mooreRel_iff.1 h)) c

theorem mooreResidual_mooreClass (p : {s // s ∈ M.reachable}) :
    (M.mooreResidual (M.mooreClass p)).val = M.acceptsFrom p.1 :=
  rfl

theorem mooreResidual_bijective : Function.Bijective M.mooreResidual := by
  constructor
  · intro c d h
    induction c using Quotient.inductionOn
    induction d using Quotient.inductionOn
    exact (M.mooreClass_eq_iff).2 (congrArg Subtype.val h)
  · rintro ⟨L, w, rfl⟩
    exact ⟨M.mooreClass ⟨M.eval w, M.mem_reachable_iff.2 ⟨w, rfl⟩⟩, rfl⟩

/-- **Moore classes are the reachable residuals.** Let $M$ be a DFA over a finite alphabet with
finitely many states. The states of Moore's minimal automaton of $M$ are in bijection with the
reachable residual languages of $M$: the bijection sends the class of a reachable state $s$ to
the continuation language of $s$, the set of words that $M$ accepts when started at $s$. -/
noncomputable def mooreEquiv : M.MooreState ≃ reachableResiduals M :=
  Equiv.ofBijective _ M.mooreResidual_bijective

omit [Fintype α] in
private theorem dfa_ext {τ : Type*} {A B : DFA α τ} (h₁ : A.step = B.step) (h₂ : A.start = B.start)
    (h₃ : A.accept = B.accept) : A = B := by
  cases A
  cases B
  cases h₁
  cases h₂
  cases h₃
  rfl

/-- **Moore's automaton is the minimal automaton.** Let $M$ be a DFA. Renaming each state of
Moore's minimal automaton of $M$, a class of reachable states, to the continuation language
accepted from its members turns Moore's automaton into exactly the minimized DFA of $M$, whose
states are the reachable continuation languages of $M$. -/
theorem reindex_mooreDFA : DFA.reindex M.mooreEquiv M.mooreDFA = minimizedDFA M := by
  have hsurj : ∀ q : reachableResiduals M, ∃ p : {s // s ∈ M.reachable},
      M.mooreEquiv (M.mooreClass p) = q := fun q => by
    obtain ⟨c, rfl⟩ := M.mooreEquiv.surjective q
    induction c using Quotient.inductionOn with
    | h p => exact ⟨p, rfl⟩
  refine dfa_ext ?_ ?_ ?_
  · funext q a
    obtain ⟨p, rfl⟩ := hsurj q
    apply Subtype.ext
    change (M.mooreEquiv
      (M.mooreDFA.step (M.mooreEquiv.symm (M.mooreEquiv (M.mooreClass p))) a)).val = _
    rw [Equiv.symm_apply_apply, mooreDFA_step_mooreClass, minimizedDFA_step_val]
    change M.acceptsFrom (M.step p.1 a) = (M.acceptsFrom p.1).leftQuotient [a]
    rw [leftQuotient_acceptsFrom, evalFrom_singleton]
  · apply Subtype.ext
    change M.acceptsFrom M.start = ((minimizedDFA M).eval []).val
    rw [minimizedDFA_eval, minimizedState_val, eval_nil]
  · ext q
    obtain ⟨p, rfl⟩ := hsurj q
    change M.mooreEquiv.symm (M.mooreEquiv (M.mooreClass p)) ∈ M.mooreDFA.accept ↔
      (leftQuotientEquivReachableResiduals M).symm (M.mooreEquiv (M.mooreClass p)) ∈
        M.accepts.toDFA.accept
    rw [Equiv.symm_apply_apply, mooreClass_mem_accept, Language.mem_accept_toDFA,
      leftQuotientEquivReachableResiduals_symm_val]
    change _ ↔ [] ∈ M.acceptsFrom p.1
    rw [mem_acceptsFrom, evalFrom_nil]

/-- **Moore's automaton has one state per Nerode class.** For a DFA $M$ over a finite alphabet
with finitely many states, Moore's minimal automaton of $M$ has exactly as many states as there
are Nerode classes of the language accepted by $M$. -/
theorem card_mooreState [Fintype (NerodeClass M.accepts)] :
    Fintype.card M.MooreState = Fintype.card (NerodeClass M.accepts) :=
  Fintype.card_congr (M.mooreEquiv.trans (nerodeClassEquivMinimizedState M).symm)

end DFA
