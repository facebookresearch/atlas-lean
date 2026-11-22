/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Automata.DA.MathlibDFA
public import CSLibExt.Computability.Automata.DA.MyhillNerodeBridge
public import CSLibExt.Computability.Languages.Congruences.Universal

/-!
# Myhill-Nerode bridges to upstream CSLib

The local quotient of words and upstream `Language.NerodeQuotient` identify the same words.
This file transports upstream minimality and uniqueness to the local Mathlib-DFA presentation.
In particular, upstream `IsMinimalAutomaton` agrees with the local
criterion that the chosen Nerode representatives reach every state of a finite recognizing DFA.
The equivalence constructed by `stateEquivResidualsOfSeparated` also satisfies upstream's
unique-minimal-automaton characterization.

The alphabet is restricted to `Type` because the pinned upstream Nerode development has that
restriction. All state types here support arbitrary universes.
`isMinimalAutomaton_ofDFA_of_accessible_separated` and
`stateEquivResidualsOfSeparated_eq_minimal_equiv` require no finiteness;
`isMinimalAutomaton_ofDFA_iff` and `unique_minimal_ofDFA` retain finite-state hypotheses.
The universe-polymorphic local regularity criterion and residual lower bound remain the canonical
APIs. Their direct upstream quotient transports are demonstrated in `NerodeUpstreamTests`;
upstream `Language.dfa_num_state_min` additionally restricts states to `Type`.

The equivalence `nerodeClassEquivNerodeQuotient` and its simp lemma
`nerodeClassEquivNerodeQuotient_mk` come from `MyhillNerodeBridge.lean`. That file's
`Type`-only bridges `Cslib.Automata.DA.FinAcc.isMinimalAutomaton_ofDFA_iff`,
`Cslib.Automata.DA.FinAcc.isMinimalAutomaton_ofDFA_of_separated` and
`Cslib.Automata.DA.FinAcc.stateEquivResidualsOfSeparated_eq_trans` are the `Type`-state cases of
`isMinimalAutomaton_ofDFA_iff`, `isMinimalAutomaton_ofDFA_of_accessible_separated` and, after
composing with `nerodeQuotientEquivResidual`, `stateEquivResidualsOfSeparated_eq_minimal_equiv`
here. `unique_minimal_ofDFA` here assumes upstream minimality and targets the local Nerode
classes, whereas `Cslib.Automata.DA.FinAcc.unique_minimal_ofDFA` assumes accessibility and state
separation and targets the upstream quotient.
-/

@[expose] public section

open scoped Computability

namespace Cslib.Language

open Cslib.Automata.DA.FinAcc

variable {Symbol : Type} {L : Language Symbol}

/-- The inverse quotient bridge sends an upstream word class to its local class. -/
@[simp]
theorem nerodeClassEquivNerodeQuotient_symm_apply (x : List Symbol) :
    (nerodeClassEquivNerodeQuotient L).symm (Quotient.mk _ x) = nerodeClass L x := by
  rw [Equiv.symm_apply_eq]
  exact (nerodeClassEquivNerodeQuotient_mk L x).symm

variable {State : Type*}

/-- For a finite recognizing DFA, upstream minimality is equivalent to the local equality
criterion: the chosen Nerode representatives reach every state. -/
theorem isMinimalAutomaton_ofDFA_iff [Finite State] (M : DFA Symbol State)
    (hM : M.accepts = L) :
    (ofDFA M).IsMinimalAutomaton L ↔
      Function.Surjective (NerodeClass.toDFAState (L := L) M) := by
  have hinj := NerodeClass.toDFAState_injective M hM
  have hcard := Nat.card_congr (nerodeClassEquivNerodeQuotient L)
  constructor
  · rintro ⟨_, hc⟩
    exact ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨hinj, hcard.trans hc.symm⟩).surjective
  · intro hsurj
    refine ⟨(accepts_ofDFA M).trans hM, ?_⟩
    exact (Nat.card_eq_of_bijective _ ⟨hinj, hsurj⟩).symm.trans hcard

/-- An accessible, state-separated Mathlib DFA satisfies upstream's recognition and state-count
predicate because its state type is equivalent to its Nerode quotient. No finiteness assumption
is required. -/
theorem isMinimalAutomaton_ofDFA_of_accessible_separated
    (M : DFA Symbol State) (hacc : Accessible M) (hsep : StateSeparated M) :
    (ofDFA M).IsMinimalAutomaton M.accepts := by
  refine ⟨accepts_ofDFA M, ?_⟩
  exact (Nat.card_congr (stateEquivResidualsOfSeparated M hacc hsep)).trans
    (Nat.card_congr (nerodeQuotientEquivResidual M.accepts)).symm

/-- Upstream `unique_minimal` gives a unique equivalence from a finite minimal Mathlib DFA
to the local Nerode classes, sending each reached state to the class of its input word. -/
theorem unique_minimal_ofDFA [Finite State] (M : DFA Symbol State)
    (hmin : (ofDFA M).IsMinimalAutomaton M.accepts) :
    ∃! e : State ≃ NerodeClass M.accepts,
      ∀ x, e (M.eval x) = nerodeClass M.accepts x := by
  let : Finite (NerodeClass M.accepts) :=
    Finite.of_injective _ (NerodeClass.toDFAState_injective M rfl)
  have hr := (isRegular_iff_finite_nerodeClass (L := M.accepts)).mpr
    inferInstance
  obtain ⟨f, hf, huniq⟩ := (ofDFA M).unique_minimal M.accepts hr hmin
  let e := nerodeClassEquivNerodeQuotient M.accepts
  refine ⟨f.trans e.symm, ?_, ?_⟩
  · intro x
    change e.symm (f (M.eval x)) = nerodeClass M.accepts x
    have hx : f (M.eval x) = Quotient.mk _ x := hf x
    rw [hx]
    exact nerodeClassEquivNerodeQuotient_symm_apply x
  · intro g hg
    have hgf : g.trans e = f := huniq _ (by
      intro x
      change e (g (M.eval x)) = Quotient.mk _ x
      rw [hg]
      exact nerodeClassEquivNerodeQuotient_mk M.accepts x)
    apply Equiv.ext
    intro q
    have hq := congrArg (fun k : State ≃ M.accepts.NerodeQuotient ↦ e.symm (k q)) hgf
    simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using hq

/-- For an accessible, state-separated DFA, every equivalence to upstream Nerode classes sending
reached states to their word classes equals the transported residual-state equivalence.
For finite state types, this is the equivalence characterized by upstream `unique_minimal`. -/
theorem stateEquivResidualsOfSeparated_eq_minimal_equiv
    (M : DFA Symbol State) (hacc : Accessible M) (hsep : StateSeparated M)
    (e : State ≃ M.accepts.NerodeQuotient)
    (he : ∀ x, e (M.eval x) = Quotient.mk _ x) :
    (stateEquivResidualsOfSeparated M hacc hsep).trans
      (nerodeQuotientEquivResidual M.accepts).symm = e := by
  apply Equiv.ext
  intro q
  obtain ⟨x, rfl⟩ := hacc q
  apply (nerodeQuotientEquivResidual M.accepts).injective
  rw [he x, Equiv.trans_apply, Equiv.apply_symm_apply]
  apply Subtype.ext
  change M.acceptsFrom (M.eval x) = M.accepts.leftQuotient x
  exact (_root_.Language.leftQuotient_accepts_apply M x).symm

end Cslib.Language
