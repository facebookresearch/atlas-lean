/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.Congruences.TransitionMinimal
public import CSLibExt.Computability.Languages.Congruences.Universal
public import CSLibExt.Computability.Automata.DA.MathlibDFA

/-!
# The syntactic monoid is the transition monoid of the minimal DFA

`TransitionMinimal.lean` identifies the syntactic monoid with the transition monoid of an
arbitrary accessible, state-separated DFA. What was missing is the instantiation at the
canonical minimal automata: Mathlib's `Language.toDFA`, the reindexed presentation
`Cslib.Language.minimizedDFA`, and the upstream canonical automaton
`Cslib.Automata.DA.FinAcc.NerodeCongruenceDA`. This file proves that all three are
accessible and state-separated (a DFA is state-separated when the map sending a state to
its continuation language is injective, and the continuation language of a residual state
is the residual itself), and instantiates the isomorphism at each of them. The upstream
case goes through the general fact that state-separatedness and accessibility are
preserved by reindexing states, applied to
`Cslib.Automata.DA.FinAcc.reindex_nerodeCongruenceDA`.

## Main results

* `Cslib.Language.toDFA_stateSeparated`, `Cslib.Language.minimizedDFA_stateSeparated`,
  `Cslib.Language.nerodeCongruenceDA_stateSeparated`: the three canonical minimal automata
  are state-separated.
* `Cslib.Language.syntacticMonoidEquivTransitionMonoidToDFA`,
  `Cslib.Language.syntacticMonoidEquivTransitionMonoidMinimizedDFA`,
  `Cslib.Language.syntacticMonoidEquivTransitionMonoidNerodeCongruenceDA`: the syntactic
  monoid is canonically isomorphic to the transition monoid of each of them, with
  `[simp]` morphism lemmas
  (`..._morphism_*`) giving the value on `syntacticMorphism` terms as
  `toTransitionMonoid`. The specializations are built by transporting the general
  equivalence along the `accepts` equalities (`accepts_toDFA`,
  `minimizedDFA_accepts`, `language_toDFA` + `nerodeCongruenceDA_language_eq`,
  via the shared `syntacticMonoidEquivTransport` helper); the morphism lemmas are what
  make them usable through the public API without unfolding those transports. The
  transport direction is the one that makes the morphism lemmas hold: the
  specialization sends the syntactic class of a word to the transition monoid element
  of that word, directly, with no `▸` cast in the statement.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

universe u v

variable {Symbol : Type u} {State : Type v}

/-- Two states are equivalent exactly when their continuation languages agree. -/
theorem stateEquivalent_iff_acceptsFrom_eq (M : DFA Symbol State) {p q : State} :
    StateEquivalent M p q ↔ M.acceptsFrom p = M.acceptsFrom q := by
  rw [stateEquivalent_iff]
  constructor
  · intro h
    ext w
    rw [DFA.mem_acceptsFrom, DFA.mem_acceptsFrom]
    exact h w
  · intro h w
    rw [← DFA.mem_acceptsFrom, ← DFA.mem_acceptsFrom, h]

/-- A DFA is state-separated when the continuation-language map is injective. -/
theorem StateSeparated.of_acceptsFrom_eq {M : DFA Symbol State}
    {f : State → Language Symbol} (hf : ∀ q, M.acceptsFrom q = f q)
    (hinj : Function.Injective f) : StateSeparated M := by
  intro p q hpq
  apply hinj
  rw [← hf p, ← hf q]
  exact (stateEquivalent_iff_acceptsFrom_eq M).mp hpq

/-- Continuation languages are preserved by reindexing states. -/
theorem acceptsFrom_reindex (M : DFA Symbol State) {State' : Type*} (e : State ≃ State')
    (q : State) : (DFA.reindex e M).acceptsFrom (e q) = M.acceptsFrom q := by
  ext w
  simp [DFA.mem_acceptsFrom, DFA.evalFrom_reindex]

/-- State-separatedness is preserved by reindexing states. -/
theorem stateSeparated_reindex (M : DFA Symbol State) {State' : Type*} (e : State ≃ State') :
    StateSeparated (DFA.reindex e M) ↔ StateSeparated M := by
  constructor
  · intro h p q hpq
    have h' : StateEquivalent (DFA.reindex e M) (e p) (e q) := by
      rw [stateEquivalent_iff_acceptsFrom_eq, acceptsFrom_reindex,
        acceptsFrom_reindex]
      exact (stateEquivalent_iff_acceptsFrom_eq M).mp hpq
    exact e.injective (h h')
  · intro h p' q' hpq'
    have h' : StateEquivalent M (e.symm p') (e.symm q') := by
      rw [stateEquivalent_iff_acceptsFrom_eq]
      have h2 := (stateEquivalent_iff_acceptsFrom_eq (DFA.reindex e M)).mp hpq'
      rw [← acceptsFrom_reindex M e (e.symm p'), ← acceptsFrom_reindex M e (e.symm q'),
        Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact h2
    exact e.symm.injective (h h')

/-- Accessibility is preserved by reindexing states. -/
theorem accessible_reindex (M : DFA Symbol State) {State' : Type*} (e : State ≃ State') :
    Accessible (DFA.reindex e M) ↔ Accessible M := by
  constructor
  · intro h q
    obtain ⟨x, hx⟩ := h (e q)
    refine ⟨x, e.injective ?_⟩
    rw [DFA.eval_reindex] at hx
    exact hx
  · intro h q'
    obtain ⟨x, hx⟩ := h (e.symm q')
    refine ⟨x, ?_⟩
    rw [DFA.eval_reindex, hx, Equiv.apply_symm_apply]

/-- Evaluation from a residual state of `L.toDFA` takes the left quotient of the residual. -/
theorem evalFrom_toDFA_val (L : Language Symbol) (q : Set.range L.leftQuotient)
    (w : List Symbol) : (L.toDFA.evalFrom q w).val = q.val.leftQuotient w := by
  induction w generalizing q with
  | nil => simp
  | cons a w ih =>
    rw [DFA.evalFrom_cons, ih, Language.step_toDFA,
      show a :: w = [a] ++ w from rfl, Language.leftQuotient_append]

/-- The continuation language of a residual state of `L.toDFA` is the residual itself. -/
theorem acceptsFrom_toDFA (L : Language Symbol) (q : Set.range L.leftQuotient) :
    L.toDFA.acceptsFrom q = q.val := by
  ext w
  simp only [DFA.mem_acceptsFrom, evalFrom_toDFA_val, Language.mem_accept_toDFA,
    Language.mem_leftQuotient, List.append_nil]

/-- Mathlib's residual-language DFA is state-separated: distinct residuals have distinct
continuation languages. -/
theorem toDFA_stateSeparated (L : Language Symbol) : StateSeparated L.toDFA :=
  StateSeparated.of_acceptsFrom_eq (fun q => acceptsFrom_toDFA L q) Subtype.val_injective

/-- The continuation language of a state of the minimized presentation is the residual it
represents. -/
theorem acceptsFrom_minimizedDFA (M : DFA Symbol State) (q : reachableResiduals M) :
    (minimizedDFA M).acceptsFrom q = q.val := by
  have h := acceptsFrom_reindex M.accepts.toDFA (leftQuotientEquivReachableResiduals M)
    ((leftQuotientEquivReachableResiduals M).symm q)
  rw [Equiv.apply_symm_apply, acceptsFrom_toDFA,
    leftQuotientEquivReachableResiduals_symm_val] at h
  exact h

/-- The minimized presentation is state-separated. -/
theorem minimizedDFA_stateSeparated (M : DFA Symbol State) :
    StateSeparated (minimizedDFA M) :=
  StateSeparated.of_acceptsFrom_eq (fun q => acceptsFrom_minimizedDFA M q)
    Subtype.val_injective

/-- The upstream canonical automaton, as a Mathlib DFA, is state-separated: it is a
reindexing of `L.toDFA`. -/
theorem nerodeCongruenceDA_stateSeparated {Alpha : Type} (l : Language Alpha) :
    StateSeparated (Cslib.Automata.DA.FinAcc.toDFA l.NerodeCongruenceDA) := by
  have h := toDFA_stateSeparated l
  rw [← Cslib.Automata.DA.FinAcc.reindex_nerodeCongruenceDA l] at h
  exact (stateSeparated_reindex _ _).mp h

/-- The upstream canonical automaton, as a Mathlib DFA, is accessible: it is a reindexing
of `L.toDFA`. -/
theorem nerodeCongruenceDA_accessible {Alpha : Type} (l : Language Alpha) :
    Accessible (Cslib.Automata.DA.FinAcc.toDFA l.NerodeCongruenceDA) := by
  have h := toDFA_accessible l
  rw [← Cslib.Automata.DA.FinAcc.reindex_nerodeCongruenceDA l] at h
  exact (accessible_reindex _ _).mp h

/-- The upstream canonical automaton, as a Mathlib DFA, accepts the language it is built
from. -/
theorem nerodeCongruenceDA_accepts {Alpha : Type} (l : Language Alpha) :
    (Cslib.Automata.DA.FinAcc.toDFA l.NerodeCongruenceDA).accepts = l := by
  rw [Cslib.Automata.DA.FinAcc.language_toDFA]
  exact _root_.Language.nerodeCongruenceDA_language_eq l

/-- Transport a syntactic-monoid equivalence along a language equality. Given
`e : SyntacticMonoid L₁ ≃* TransitionMonoid M` and `h : L₁ = L₂`, this is the
`SyntacticMonoid L₂ ≃* TransitionMonoid M` obtained by rewriting `h` in `e`; on
`syntacticMorphism` terms it sends the syntactic class of a word to the same
transition monoid element. The three canonical specializations below are instances
of this helper at the `accepts` equalities. -/
noncomputable def syntacticMonoidEquivTransport {Symbol : Type u}
    {L₁ L₂ : Language Symbol} {M : DFA Symbol State} (h : L₁ = L₂)
    (e : SyntacticMonoid L₁ ≃* TransitionMonoid M) : SyntacticMonoid L₂ ≃* TransitionMonoid M :=
  h ▸ e

/-- The transported equivalence sends the syntactic class of a word to the same
transition monoid element as the original equivalence. Stated in simp-normal form,
at the coercion `(x : SyntacticMonoid L₂)`, since `simp` rewrites
`syntacticMorphism L₂ x` to that coercion (`syntacticMorphism_apply`). -/
theorem syntacticMonoidEquivTransport_morphism {Symbol : Type u}
    {L₁ L₂ : Language Symbol} {M : DFA Symbol State} (h : L₁ = L₂)
    (e : SyntacticMonoid L₁ ≃* TransitionMonoid M) (x : FreeMonoid Symbol) :
    syntacticMonoidEquivTransport h e (x : SyntacticMonoid L₂) =
      e (x : SyntacticMonoid L₁) := by
  subst h
  rfl

/-- **The syntactic monoid is the transition monoid of Mathlib's canonical minimal DFA.** -/
noncomputable def syntacticMonoidEquivTransitionMonoidToDFA (L : Language Symbol) :
    SyntacticMonoid L ≃* TransitionMonoid L.toDFA :=
  syntacticMonoidEquivTransport (Language.accepts_toDFA (L := L))
    (syntacticMonoidEquivTransitionMonoid L.toDFA (toDFA_accessible L) (toDFA_stateSeparated L))

/-- The canonical isomorphism for `L.toDFA` sends the syntactic class of a word to the
transition monoid element of that word. Stated in simp-normal form: `simp` rewrites
`syntacticMorphism L x` to the coercion `(x : SyntacticMonoid L)`
(`syntacticMorphism_apply`), so the lemma is stated at the coercion. -/
@[simp]
theorem syntacticMonoidEquivTransitionMonoidToDFA_morphism (L : Language Symbol)
    (x : FreeMonoid Symbol) :
    syntacticMonoidEquivTransitionMonoidToDFA L (x : SyntacticMonoid L) =
      toTransitionMonoid L.toDFA x := by
  simp only [syntacticMonoidEquivTransitionMonoidToDFA,
    syntacticMonoidEquivTransport_morphism]
  change (syntacticMonoidEquivTransitionMonoid L.toDFA (toDFA_accessible L)
    (toDFA_stateSeparated L)) ((syntacticMorphism L.toDFA.accepts) x) =
    toTransitionMonoid L.toDFA x
  exact syntacticMonoidEquivTransitionMonoid_morphism L.toDFA (toDFA_accessible L)
    (toDFA_stateSeparated L) x

/-- **The syntactic monoid is the transition monoid of the minimized presentation.** -/
noncomputable def syntacticMonoidEquivTransitionMonoidMinimizedDFA (M : DFA Symbol State) :
    SyntacticMonoid M.accepts ≃* TransitionMonoid (minimizedDFA M) :=
  syntacticMonoidEquivTransport (minimizedDFA_accepts M)
    (syntacticMonoidEquivTransitionMonoid (minimizedDFA M) (minimizedDFA_accessible M)
      (minimizedDFA_stateSeparated M))

/-- The canonical isomorphism for `minimizedDFA M` sends the syntactic class of a word
to the transition monoid element of that word. Stated in simp-normal form, as in the
`toDFA` case. -/
@[simp]
theorem syntacticMonoidEquivTransitionMonoidMinimizedDFA_morphism (M : DFA Symbol State)
    (x : FreeMonoid Symbol) :
    syntacticMonoidEquivTransitionMonoidMinimizedDFA M (x : SyntacticMonoid M.accepts) =
      toTransitionMonoid (minimizedDFA M) x := by
  simp only [syntacticMonoidEquivTransitionMonoidMinimizedDFA,
    syntacticMonoidEquivTransport_morphism]
  change (syntacticMonoidEquivTransitionMonoid (minimizedDFA M) (minimizedDFA_accessible M)
    (minimizedDFA_stateSeparated M)) ((syntacticMorphism (minimizedDFA M).accepts) x) =
    toTransitionMonoid (minimizedDFA M) x
  exact syntacticMonoidEquivTransitionMonoid_morphism (minimizedDFA M)
    (minimizedDFA_accessible M) (minimizedDFA_stateSeparated M) x

/-- **The syntactic monoid is the transition monoid of the upstream canonical minimal
automaton.** -/
noncomputable def syntacticMonoidEquivTransitionMonoidNerodeCongruenceDA
    {Alpha : Type} (l : Language Alpha) :
    SyntacticMonoid l ≃* TransitionMonoid
      (Cslib.Automata.DA.FinAcc.toDFA l.NerodeCongruenceDA) :=
  syntacticMonoidEquivTransport (nerodeCongruenceDA_accepts l)
    (syntacticMonoidEquivTransitionMonoid _
      (nerodeCongruenceDA_accessible l) (nerodeCongruenceDA_stateSeparated l))

/-- The canonical isomorphism for the upstream canonical automaton sends the syntactic
class of a word to the transition monoid element of that word. Stated in simp-normal
form, as in the `toDFA` case. -/
@[simp]
theorem syntacticMonoidEquivTransitionMonoidNerodeCongruenceDA_morphism {Alpha : Type}
    (l : Language Alpha) (x : FreeMonoid Alpha) :
    syntacticMonoidEquivTransitionMonoidNerodeCongruenceDA l (x : SyntacticMonoid l) =
      toTransitionMonoid (Cslib.Automata.DA.FinAcc.toDFA l.NerodeCongruenceDA) x := by
  simp only [syntacticMonoidEquivTransitionMonoidNerodeCongruenceDA,
    syntacticMonoidEquivTransport_morphism]
  change (syntacticMonoidEquivTransitionMonoid _
    (nerodeCongruenceDA_accessible l) (nerodeCongruenceDA_stateSeparated l))
      ((syntacticMorphism (Cslib.Automata.DA.FinAcc.toDFA l.NerodeCongruenceDA).accepts) x) =
    toTransitionMonoid (Cslib.Automata.DA.FinAcc.toDFA l.NerodeCongruenceDA) x
  exact syntacticMonoidEquivTransitionMonoid_morphism _
    (nerodeCongruenceDA_accessible l) (nerodeCongruenceDA_stateSeparated l) x

end Cslib.Language
