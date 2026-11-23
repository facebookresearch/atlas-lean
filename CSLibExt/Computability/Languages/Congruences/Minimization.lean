/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `290c48922e071d1e4267dd103a14e73b547adf60`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module


public import CSLibExt.Computability.Languages.Congruences.Minimality

/-!
# Semantic minimization of deterministic automata

Mathlib's `Language.toDFA` is already the canonical DFA whose states are reachable left quotients.
This file does not build a parallel automaton. Instead, it identifies those states with the
continuation languages of the reachable states of an arbitrary DFA `M`, then reindexes
`M.accepts.toDFA` along that equivalence.

The resulting presentation accepts the same language, is accessible, and has one state for every
Nerode class. It is useful when minimization should be described in terms of the source automaton's
observable state behavior rather than directly in terms of words.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe u v

variable {Symbol : Type u} {State : Type v}

/-- **Left quotients of continuation languages.** Let $M$ be a DFA, write $\delta^*(q, x)$ for
the state $M$ reaches from the state $q$ by reading the word $x$, and let $L_M(q)$ be the
language of words accepted by $M$ when started in $q$. For every state $q$ and every word $x$,
the left quotient $\{z : xz \in L_M(q)\}$ of $L_M(q)$ by $x$ equals $L_M(\delta^*(q, x))$. -/
theorem leftQuotient_acceptsFrom (M : DFA Symbol State) (q : State) (x : List Symbol) :
    (M.acceptsFrom q).leftQuotient x = M.acceptsFrom (M.evalFrom q x) := by
  ext z
  simp only [Language.mem_leftQuotient, DFA.mem_acceptsFrom, DFA.evalFrom_of_append]

/-- **Residual reached by a word.** For a DFA $M$ and a word $x$, the minimized state of $x$ is the
language accepted by $M$ starting from the state that $M$ reaches on reading $x$ from its start
state, viewed as an element of the reachable residuals of $M$. -/
def minimizedState (M : DFA Symbol State) (x : List Symbol) : reachableResiduals M :=
  ⟨M.acceptsFrom (M.eval x), ⟨x, rfl⟩⟩

@[simp]
theorem minimizedState_val (M : DFA Symbol State) (x : List Symbol) :
    (minimizedState M x).val = M.acceptsFrom (M.eval x) :=
  rfl

theorem minimizedState_append (M : DFA Symbol State) (x y : List Symbol) :
    (minimizedState M (x ++ y)).val = (minimizedState M x).val.leftQuotient y := by
  simp only [minimizedState_val, DFA.eval, DFA.evalFrom_of_append]
  rw [leftQuotient_acceptsFrom]

theorem minimizedState_eq_iff_stateEquivalent (M : DFA Symbol State) {x y : List Symbol} :
    minimizedState M x = minimizedState M y ↔ StateEquivalent M (M.eval x) (M.eval y) := by
  rw [Subtype.ext_iff]
  rfl

theorem minimizedState_eq_iff_nerodeRel (M : DFA Symbol State) {x y : List Symbol} :
    minimizedState M x = minimizedState M y ↔ nerodeRel M.accepts x y := by
  rw [minimizedState_eq_iff_stateEquivalent, nerodeRel_iff_stateEquivalent]

/-- **Left quotients as reachable residuals.** Let $M$ be a DFA accepting the language $L$. The
set of left quotients $\{z : xz \in L\}$ of $L$ by words $x$ equals the set of reachable
residuals of $M$ (the languages accepted by $M$ from the states it reaches from its start
state). The bijection from the first set to the second sends each language to itself. -/
noncomputable def leftQuotientEquivReachableResiduals (M : DFA Symbol State) :
    Set.range M.accepts.leftQuotient ≃ reachableResiduals M where
  toFun q := ⟨q.val, by
    rw [reachableResiduals_eq_range_leftQuotient]
    exact q.property⟩
  invFun q := ⟨q.val, by
    rw [← reachableResiduals_eq_range_leftQuotient]
    exact q.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

@[simp]
theorem leftQuotientEquivReachableResiduals_val (M : DFA Symbol State)
    (q : Set.range M.accepts.leftQuotient) :
    (leftQuotientEquivReachableResiduals M q).val = q.val :=
  rfl

@[simp]
theorem leftQuotientEquivReachableResiduals_symm_val (M : DFA Symbol State)
    (q : reachableResiduals M) :
    ((leftQuotientEquivReachableResiduals M).symm q).val = q.val :=
  rfl

/-- **Minimized DFA.** Let $M$ be a DFA accepting the language $L$. The minimized DFA of $M$
has as states the reachable residuals of $M$, that is, the languages accepted by $M$ from the
states it reaches from its start state. Its start state is $L$; on a letter $a$ it moves from
a state $K$ to the left quotient $\{z : az \in K\}$; and its accepting states are those that
contain the empty word.

It is the canonical automaton of $L$, whose states are the left quotients of $L$, with each
state renamed to the same language viewed as a reachable residual of $M$. -/
noncomputable def minimizedDFA (M : DFA Symbol State) : DFA Symbol (reachableResiduals M) :=
  DFA.reindex (leftQuotientEquivReachableResiduals M) M.accepts.toDFA

/-- **States reached in the residual-language DFA.** For every language $L$ and every word $x$, the
state that the residual-language DFA of $L$ reaches on reading $x$ is the left quotient
$x^{-1}L = \{z : xz \in L\}$. This automaton has the left quotients of $L$ as states, start state
$L$, transition from $K$ on a letter $a$ to $a^{-1}K$, and accepts $K$ when $K$ contains the empty
word. -/
@[simp]
theorem toDFA_eval_val (L : Language Symbol) (x : List Symbol) :
    (L.toDFA.eval x).val = L.leftQuotient x := by
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih =>
      rw [DFA.eval_append_singleton, Language.step_toDFA, ih,
        Language.leftQuotient_append]

/-- **Evaluation in the minimized DFA agrees with the left-quotient automaton.** Let $M$ be a
DFA accepting the language $L$, and consider the automaton whose states are the left quotients
of $L$, with start state $L$, moving from $K$ on a letter $a$ to $\{z : az \in K\}$. For every
word $x$, the state that the minimized DFA of $M$ reaches on $x$, carried to the left quotients
of $L$ by the bijection that sends each language to itself, is the state that this automaton
reaches on $x$. -/
@[simp]
theorem minimizedDFA_eval_equiv (M : DFA Symbol State) (x : List Symbol) :
    (leftQuotientEquivReachableResiduals M).symm ((minimizedDFA M).eval x) =
      M.accepts.toDFA.eval x := by
  simp [minimizedDFA]

/-- **States reached in the minimized DFA.** For every DFA $M$ and every word $x$, the state that
the minimized DFA of $M$ reaches on $x$ is the language accepted by $M$ from the state that $M$
reaches on $x$. -/
@[simp]
theorem minimizedDFA_eval (M : DFA Symbol State) (x : List Symbol) :
    (minimizedDFA M).eval x = minimizedState M x := by
  apply Subtype.ext
  have h := congrArg Subtype.val (minimizedDFA_eval_equiv M x)
  simpa only [leftQuotientEquivReachableResiduals_symm_val, toDFA_eval_val,
    minimizedState_val, Language.leftQuotient_accepts_apply] using h

/-- **Transitions of the minimized DFA.** Let $M$ be a DFA. For every reachable residual $K$ of
$M$ (a state of the minimized DFA of $M$) and every letter $a$, the minimized DFA of $M$ moves
from $K$ on input $a$ to the left quotient $\{z : az \in K\}$ of $K$ by $a$. -/
@[simp]
theorem minimizedDFA_step_val (M : DFA Symbol State) (q : reachableResiduals M) (a : Symbol) :
    ((minimizedDFA M).step q a).val = q.val.leftQuotient [a] := by
  change (leftQuotientEquivReachableResiduals M
    (M.accepts.toDFA.step ((leftQuotientEquivReachableResiduals M).symm q) a)).val = _
  rw [leftQuotientEquivReachableResiduals_val, Language.step_toDFA]
  rfl

/-- **Transitions of the minimized DFA on reached states.** Let $M$ be a DFA, and for a word $x$
let $[x]$ be the language accepted by $M$ from the state that $M$ reaches on $x$. For every word
$x$ and every letter $a$, the minimized DFA of $M$ moves from the state $[x]$ on input $a$ to the
state $[xa]$. -/
@[simp]
theorem minimizedDFA_step_minimizedState (M : DFA Symbol State) (x : List Symbol) (a : Symbol) :
    (minimizedDFA M).step (minimizedState M x) a = minimizedState M (x ++ [a]) := by
  apply Subtype.ext
  rw [minimizedDFA_step_val, minimizedState_append]

/-- **The minimized DFA accepts the same language.** For every DFA $M$, the minimized DFA of $M$
accepts exactly the language accepted by $M$. -/
@[simp]
theorem minimizedDFA_accepts (M : DFA Symbol State) :
    (minimizedDFA M).accepts = M.accepts := by
  simp [minimizedDFA]

/-- **The residual-language DFA is accessible.** For every language $L$, the residual-language DFA
of $L$ is accessible. This automaton has as states the left quotients $x^{-1}L = \{z : xz \in L\}$
for words $x$, start state $L$, transition from $K$ on a letter $a$ to $a^{-1}K$, and accepts $K$
when $K$ contains the empty word. -/
theorem toDFA_accessible (L : Language Symbol) : Accessible L.toDFA := by
  intro q
  obtain ⟨x, hx⟩ := q.property
  refine ⟨x, Subtype.ext ?_⟩
  rw [toDFA_eval_val]
  exact hx

/-- **The minimized DFA is accessible.** For every DFA $M$, every state of the minimized DFA of
$M$ is reached from its start state by reading some word. -/
theorem minimizedDFA_accessible (M : DFA Symbol State) : Accessible (minimizedDFA M) := by
  intro q
  obtain ⟨x, hx⟩ := toDFA_accessible M.accepts
    ((leftQuotientEquivReachableResiduals M).symm q)
  refine ⟨x, ?_⟩
  rw [minimizedDFA, DFA.eval_reindex, hx, Equiv.apply_symm_apply]

/-- **Nerode classes and reachable residuals.** For a DFA $M$ accepting the language $L$, there is a
bijection from the Nerode classes of $L$ to the reachable residuals of $M$; it sends the class of a
word $x$ to the left quotient $x^{-1}L = \{z : xz \in L\}$. -/
noncomputable def nerodeClassEquivMinimizedState (M : DFA Symbol State) :
    NerodeClass M.accepts ≃ reachableResiduals M :=
  nerodeClassEquivReachableResiduals M rfl

/-- **Reachable residuals of the minimized DFA.** Let $M$ be a DFA accepting the language $L$.
The reachable residuals of the minimized DFA of $M$ and the reachable residuals of $M$ both form
the set of left quotients $x^{-1}L = \{z : xz \in L\}$ of $L$ by words $x$, and this is the
bijection from the first set to the second that sends each language to itself.

It is built as the composite of the bijections from the Nerode classes of $L$ to both sets, each
sending the class of a word $x$ to $x^{-1}L$; so minimizing the minimized DFA again gives the
same state space. -/
noncomputable def minimizedStateEquivIterated (M : DFA Symbol State) :
    reachableResiduals (minimizedDFA M) ≃ reachableResiduals M :=
  (nerodeClassEquivReachableResiduals (minimizedDFA M) (minimizedDFA_accepts M)).symm.trans
    (nerodeClassEquivMinimizedState M)

/-- **When finite, the minimized DFA has as many states as there are Nerode classes.** Let $M$
be a DFA accepting the language $L$. If the set of reachable residuals of $M$ (the states of the
minimized DFA of $M$) and the set of Nerode classes of $L$ are both finite, then they have the
same number of elements. -/
theorem minimizedDFA_card_eq_nerode (M : DFA Symbol State) [Fintype (reachableResiduals M)]
    [Fintype (NerodeClass M.accepts)] :
    Fintype.card (reachableResiduals M) = Fintype.card (NerodeClass M.accepts) := by
  exact Fintype.card_congr (nerodeClassEquivMinimizedState M).symm

end Cslib.Language
