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

/-- Reading `x` from a state transforms its continuation language by the left quotient by `x`. -/
theorem leftQuotient_acceptsFrom (M : DFA Symbol State) (q : State) (x : List Symbol) :
    (M.acceptsFrom q).leftQuotient x = M.acceptsFrom (M.evalFrom q x) := by
  ext z
  simp only [Language.mem_leftQuotient, DFA.mem_acceptsFrom, DFA.evalFrom_of_append]

/-- The semantic state reached by a word in `M`. -/
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

/-- The range of left quotients and the reachable continuation languages are the same semantic
state space. -/
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

/-- The canonical residual-language DFA, presented using reachable continuation languages of `M`.
This is a reindexing of Mathlib's `Language.toDFA`, not a second implementation. -/
noncomputable def minimizedDFA (M : DFA Symbol State) : DFA Symbol (reachableResiduals M) :=
  DFA.reindex (leftQuotientEquivReachableResiduals M) M.accepts.toDFA

/-- Evaluation in Mathlib's residual-language DFA reaches the left quotient by the input word. -/
@[simp]
theorem toDFA_eval_val (L : Language Symbol) (x : List Symbol) :
    (L.toDFA.eval x).val = L.leftQuotient x := by
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih =>
      rw [DFA.eval_append_singleton, Language.step_toDFA, ih,
        Language.leftQuotient_append]

/-- Reindexing exposes exactly the existing residual-language evaluation. -/
@[simp]
theorem minimizedDFA_eval_equiv (M : DFA Symbol State) (x : List Symbol) :
    (leftQuotientEquivReachableResiduals M).symm ((minimizedDFA M).eval x) =
      M.accepts.toDFA.eval x := by
  simp [minimizedDFA]

/-- Evaluating the minimized presentation reaches the source automaton's continuation language
after the same word. -/
@[simp]
theorem minimizedDFA_eval (M : DFA Symbol State) (x : List Symbol) :
    (minimizedDFA M).eval x = minimizedState M x := by
  apply Subtype.ext
  have h := congrArg Subtype.val (minimizedDFA_eval_equiv M x)
  simpa only [leftQuotientEquivReachableResiduals_symm_val, toDFA_eval_val,
    minimizedState_val, Language.leftQuotient_accepts_apply] using h

/-- A transition in the minimized presentation takes the left quotient of the represented
continuation language by the input letter. -/
@[simp]
theorem minimizedDFA_step_val (M : DFA Symbol State) (q : reachableResiduals M) (a : Symbol) :
    ((minimizedDFA M).step q a).val = q.val.leftQuotient [a] := by
  change (leftQuotientEquivReachableResiduals M
    (M.accepts.toDFA.step ((leftQuotientEquivReachableResiduals M).symm q) a)).val = _
  rw [leftQuotientEquivReachableResiduals_val, Language.step_toDFA]
  rfl

/-- The transition reached from a semantic state represented by `x` is the semantic state
represented by appending the input letter. -/
@[simp]
theorem minimizedDFA_step_minimizedState (M : DFA Symbol State) (x : List Symbol) (a : Symbol) :
    (minimizedDFA M).step (minimizedState M x) a = minimizedState M (x ++ [a]) := by
  apply Subtype.ext
  rw [minimizedDFA_step_val, minimizedState_append]

/-- The reindexed minimized automaton recognizes exactly the original language. -/
@[simp]
theorem minimizedDFA_accepts (M : DFA Symbol State) :
    (minimizedDFA M).accepts = M.accepts := by
  simp [minimizedDFA]

/-- Mathlib's residual-language DFA is accessible. -/
theorem toDFA_accessible (L : Language Symbol) : Accessible L.toDFA := by
  intro q
  obtain ⟨x, hx⟩ := q.property
  refine ⟨x, Subtype.ext ?_⟩
  rw [toDFA_eval_val]
  exact hx

/-- The reachable-residual presentation remains accessible after reindexing. -/
theorem minimizedDFA_accessible (M : DFA Symbol State) : Accessible (minimizedDFA M) := by
  intro q
  obtain ⟨x, hx⟩ := toDFA_accessible M.accepts
    ((leftQuotientEquivReachableResiduals M).symm q)
  refine ⟨x, ?_⟩
  rw [minimizedDFA, DFA.eval_reindex, hx, Equiv.apply_symm_apply]

/-- The states of the minimized presentation are exactly the Nerode classes of the accepted
language. -/
noncomputable def nerodeClassEquivMinimizedState (M : DFA Symbol State) :
    NerodeClass M.accepts ≃ reachableResiduals M :=
  nerodeClassEquivReachableResiduals M rfl

/-- Semantic minimization is idempotent at the level of state spaces. -/
noncomputable def minimizedStateEquivIterated (M : DFA Symbol State) :
    reachableResiduals (minimizedDFA M) ≃ reachableResiduals M :=
  (nerodeClassEquivReachableResiduals (minimizedDFA M) (minimizedDFA_accepts M)).symm.trans
    (nerodeClassEquivMinimizedState M)

/-- When finite, the semantic presentation attains the universal Nerode lower bound. -/
theorem minimizedDFA_card_eq_nerode (M : DFA Symbol State) [Fintype (reachableResiduals M)]
    [Fintype (NerodeClass M.accepts)] :
    Fintype.card (reachableResiduals M) = Fintype.card (NerodeClass M.accepts) := by
  exact Fintype.card_congr (nerodeClassEquivMinimizedState M).symm

end Cslib.Language
