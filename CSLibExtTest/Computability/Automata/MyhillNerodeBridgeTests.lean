/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Automata.DA.MyhillNerodeBridge

/-!
# Tests for the bridges between the local Myhill-Nerode stack and upstream

* The local quotient criterion and lower bound follow from upstream
  `Language.IsRegular.iff_finite_nerodeQuotient` and `Language.dfa_num_state_min`.
* Upstream `IsMinimalAutomaton` of a Mathlib DFA is the local surjectivity criterion.
* The parity DFA is accessible and state-separated, hence upstream-minimal, and its local
  uniqueness equivalence is upstream's unique isomorphism.
-/

@[expose] public section

namespace Cslib.Automata.DA.FinAcc.MyhillNerodeBridgeTests

open Cslib.Language

/-- Number of `true`s modulo 2; accept an even count. -/
def parity : DFA Bool (Fin 2) := ⟨fun s b => if b then s + 1 else s, 0, {0}⟩

example (x : List Bool) :
    nerodeClassEquivNerodeQuotient parity.accepts ⟦x⟧ = ⟦x⟧ :=
  nerodeClassEquivNerodeQuotient_mk _ x

/-- The local quotient form of Myhill-Nerode, derived from upstream's. -/
example {Symbol : Type} (L : Language Symbol) : L.IsRegular ↔ Finite (NerodeClass L) := by
  rw [Language.IsRegular.iff_finite_nerodeQuotient, finite_nerodeClass_iff_finite_nerodeQuotient]

/-- The local residual lower bound, derived from upstream `dfa_num_state_min`. -/
example {Symbol State : Type} [Finite State] (M : DFA Symbol State) {L : Language Symbol}
    (hM : M.accepts = L) : Nat.card (Set.range L.leftQuotient) ≤ Nat.card State := by
  rw [← Nat.card_congr (nerodeQuotientEquivResidual L)]
  exact natCard_nerodeQuotient_le_natCard_state M hM

example : Nat.card parity.accepts.NerodeQuotient ≤ 2 := by
  simpa using natCard_nerodeQuotient_le_natCard_state parity rfl

example (x : List Bool) : (ofDFA parity).mtr (ofDFA parity).start x = parity.eval x :=
  mtr_ofDFA_start parity x

example {Symbol State : Type} [Finite State] (M : DFA Symbol State) :
    IsMinimalAutomaton (ofDFA M) M.accepts ↔
      Function.Surjective (NerodeClass.toDFAState (L := M.accepts) M) :=
  isMinimalAutomaton_ofDFA_iff M

theorem parity_accessible : Accessible parity := by
  intro q
  fin_cases q
  · exact ⟨[], rfl⟩
  · exact ⟨[true], rfl⟩

theorem parity_separated : StateSeparated parity := by
  intro p q hpq
  have h := congrArg (fun L : Language Bool => [] ∈ L) hpq
  simp only [DFA.mem_acceptsFrom, DFA.evalFrom_nil, parity] at h
  fin_cases p <;> fin_cases q <;> simp_all

example : IsMinimalAutomaton (ofDFA parity) parity.accepts :=
  isMinimalAutomaton_ofDFA_of_separated parity parity_accessible parity_separated

example : Function.Surjective (NerodeClass.toDFAState (L := parity.accepts) parity) :=
  (isMinimalAutomaton_ofDFA_iff parity).mp
    (isMinimalAutomaton_ofDFA_of_separated parity parity_accessible parity_separated)

example : ∃! φ : Fin 2 ≃ parity.accepts.NerodeQuotient, ∀ x, φ (parity.eval x) = ⟦x⟧ :=
  unique_minimal_ofDFA parity parity_accessible parity_separated

/-- The local uniqueness equivalence is the upstream unique isomorphism, read through residuals. -/
example : ∃ φ : Fin 2 ≃ parity.accepts.NerodeQuotient, (∀ x, φ (parity.eval x) = ⟦x⟧) ∧
    stateEquivResidualsOfSeparated parity parity_accessible parity_separated =
      φ.trans (nerodeQuotientEquivResidual parity.accepts) := by
  obtain ⟨φ, hφ, -⟩ := unique_minimal_ofDFA parity parity_accessible parity_separated
  exact ⟨φ, hφ, stateEquivResidualsOfSeparated_eq_trans _ _ _ φ hφ⟩

end Cslib.Automata.DA.FinAcc.MyhillNerodeBridgeTests
