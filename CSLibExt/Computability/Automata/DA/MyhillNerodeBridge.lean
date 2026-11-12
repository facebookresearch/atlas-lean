/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The local Myhill-Nerode stack and the upstream theorems
-/
module

public import CSLibExt.Computability.Automata.DA.MathlibDFA
public import CSLibExt.Computability.Languages.Congruences.Universal

/-!
# The local Myhill-Nerode stack and the upstream theorems

`CSLibExt/Computability/Languages/Congruences/` proves the Myhill-Nerode theorem for Mathlib
`DFA`s: the quotient criterion `Cslib.Language.isRegular_iff_finite_nerodeClass`, the state lower
bound `Cslib.Language.natCard_range_leftQuotient_le_natCard_state`, the minimality criterion
`Cslib.Language.card_nerodeClass_eq_card_state_iff`, and uniqueness of the minimal automaton
`Cslib.Language.stateEquivResidualsOfSeparated`. Pinned upstream CSLib proves the same three parts
for `Cslib.Automata.DA.FinAcc` in `Cslib.Computability.Languages.MyhillNerode`:
`Language.IsRegular.iff_finite_nerodeQuotient`, `Language.dfa_num_state_min`,
`Cslib.Automata.DA.FinAcc.IsMinimalAutomaton` and `Cslib.Automata.DA.FinAcc.unique_minimal`.
This file states how they correspond.

* `Cslib.Language.nerodeClassEquivNerodeQuotient`: the local Nerode classes are the upstream
  Nerode quotient; `Cslib.Language.finite_nerodeClass_iff_finite_nerodeQuotient` follows.
* `Cslib.Language.natCard_nerodeQuotient_le_natCard_state`: upstream `dfa_num_state_min` for a
  Mathlib `DFA`, from which the local lower bound follows.
* `Cslib.Automata.DA.FinAcc.isMinimalAutomaton_ofDFA_iff`: upstream minimality of a Mathlib `DFA`
  is the local criterion, surjectivity of `Cslib.Language.NerodeClass.toDFAState`.
* `Cslib.Automata.DA.FinAcc.isMinimalAutomaton_ofDFA_of_separated`,
  `Cslib.Automata.DA.FinAcc.unique_minimal_ofDFA` and
  `Cslib.Automata.DA.FinAcc.stateEquivResidualsOfSeparated_eq_trans`: an accessible,
  state-separated DFA is upstream-minimal, and the local equivalence
  `stateEquivResidualsOfSeparated` is the unique isomorphism of `unique_minimal`, read through
  `nerodeQuotientEquivResidual`.

The local versions stay. They are stated for Mathlib `DFA` (the representation used by
`Language.toDFA`, `DFA.reindex` and the minimization files) and for an alphabet and state type in
arbitrary universes, whereas the upstream theorems fix both to `Type`. The bridges here therefore
carry `Symbol State : Type`.
-/

@[expose] public section

namespace Cslib.Language

open Cslib.Automata.DA.FinAcc

variable {Symbol : Type} (L : Language Symbol)

/-- The local Nerode classes of `L` are the classes of the upstream Nerode congruence
`Language.NerodeQuotient`: both are the residual languages of `L`. -/
noncomputable def nerodeClassEquivNerodeQuotient : NerodeClass L ≃ L.NerodeQuotient :=
  (nerodeClassEquivResidual L).trans (nerodeQuotientEquivResidual L).symm

/-- `nerodeClassEquivNerodeQuotient` sends the local class of a word to its upstream class. -/
@[simp]
theorem nerodeClassEquivNerodeQuotient_mk (x : List Symbol) :
    nerodeClassEquivNerodeQuotient L ⟦x⟧ = ⟦x⟧ := by
  apply (nerodeQuotientEquivResidual L).injective
  simp only [nerodeClassEquivNerodeQuotient, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-- The local and upstream Nerode quotients are finite together, so the local quotient form of
Myhill-Nerode (`isRegular_iff_finite_nerodeClass`) and upstream
`Language.IsRegular.iff_finite_nerodeQuotient` are the same statement. -/
theorem finite_nerodeClass_iff_finite_nerodeQuotient :
    Finite (NerodeClass L) ↔ Finite L.NerodeQuotient :=
  Equiv.finite_iff (nerodeClassEquivNerodeQuotient L)

variable {L}

/-- Upstream `Language.dfa_num_state_min` for a Mathlib `DFA`: a finite DFA accepting `L` has at
least as many states as `L` has upstream Nerode classes. -/
theorem natCard_nerodeQuotient_le_natCard_state {State : Type} [Finite State]
    (M : DFA Symbol State) (hM : M.accepts = L) :
    Nat.card L.NerodeQuotient ≤ Nat.card State := by
  have h := Language.dfa_num_state_min (M := ofDFA M)
  rwa [accepts_ofDFA, hM] at h

end Cslib.Language

namespace Cslib.Automata.DA.FinAcc

open Cslib.Language

variable {Symbol State : Type}

/-- Running the upstream form of a Mathlib `DFA` from its start state is `DFA.eval`. -/
@[simp]
theorem mtr_ofDFA_start (M : DFA Symbol State) (x : List Symbol) :
    (ofDFA M).mtr (ofDFA M).start x = M.eval x :=
  (toDFA_evalFrom (ofDFA M) M.start x).symm

/-- Upstream minimality (`IsMinimalAutomaton`) of a Mathlib `DFA` is the local minimality
criterion of `card_nerodeClass_eq_card_state_iff`: every state is reached by a chosen Nerode
class representative. -/
theorem isMinimalAutomaton_ofDFA_iff [Finite State] (M : DFA Symbol State) :
    IsMinimalAutomaton (ofDFA M) M.accepts ↔
      Function.Surjective (NerodeClass.toDFAState (L := M.accepts) M) := by
  have := Fintype.ofFinite State
  have : Finite (NerodeClass M.accepts) :=
    Finite.of_injective _ (NerodeClass.toDFAState_injective M rfl)
  have := Fintype.ofFinite (NerodeClass M.accepts)
  rw [← card_nerodeClass_eq_card_state_iff M rfl, IsMinimalAutomaton, accepts_ofDFA,
    ← Nat.card_congr (nerodeClassEquivNerodeQuotient M.accepts), Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  exact ⟨fun h => h.2.symm, fun h => ⟨rfl, h.symm⟩⟩

/-- An accessible, state-separated DFA is minimal in the upstream sense. -/
theorem isMinimalAutomaton_ofDFA_of_separated (M : DFA Symbol State)
    (hacc : Accessible M) (hsep : StateSeparated M) :
    IsMinimalAutomaton (ofDFA M) M.accepts :=
  ⟨accepts_ofDFA M, Nat.card_congr ((stateEquivResidualsOfSeparated M hacc hsep).trans
    (nerodeQuotientEquivResidual M.accepts).symm)⟩

/-- Upstream `unique_minimal` for an accessible, state-separated finite Mathlib `DFA`: there is
exactly one isomorphism from its states to the upstream Nerode quotient sending the state reached
by `x` to the class of `x`. -/
theorem unique_minimal_ofDFA [Finite State] (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) :
    ∃! φ : State ≃ M.accepts.NerodeQuotient, ∀ x, φ (M.eval x) = ⟦x⟧ := by
  have hr : M.accepts.IsRegular := ⟨State, Fintype.ofFinite State, M, rfl⟩
  simpa only [mtr_ofDFA_start] using
    unique_minimal (M := ofDFA M) M.accepts hr (isMinimalAutomaton_ofDFA_of_separated M hacc hsep)

/-- The local uniqueness equivalence `stateEquivResidualsOfSeparated` is the isomorphism of
upstream `unique_minimal`, followed by `nerodeQuotientEquivResidual`. -/
theorem stateEquivResidualsOfSeparated_eq_trans (M : DFA Symbol State) (hacc : Accessible M)
    (hsep : StateSeparated M) (φ : State ≃ M.accepts.NerodeQuotient)
    (hφ : ∀ x, φ (M.eval x) = ⟦x⟧) :
    stateEquivResidualsOfSeparated M hacc hsep =
      φ.trans (nerodeQuotientEquivResidual M.accepts) := by
  refine Equiv.ext fun q => ?_
  obtain ⟨x, rfl⟩ := hacc q
  apply Subtype.ext
  change M.acceptsFrom (M.eval x) = (nerodeQuotientEquivResidual M.accepts (φ (M.eval x))).val
  rw [hφ]
  exact (Language.leftQuotient_accepts_apply M x).symm

end Cslib.Automata.DA.FinAcc
