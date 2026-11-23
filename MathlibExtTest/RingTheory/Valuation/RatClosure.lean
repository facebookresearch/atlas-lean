/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.RatClosure

@[expose] public section

/-- `exactSource` consumer with the original binders. -/
example (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime r) :
    ∃ L₁ L₂ : Subfield A.valuation.Completion,
      ValuationSubring.ratClosure A ≤ L₁ ∧ ValuationSubring.ratClosure A ≤ L₂ ∧
      IsClosed (L₁ : Set A.valuation.Completion) ∧
      IsClosed (L₂ : Set A.valuation.Completion) ∧
      L₁ ⊓ L₂ = ValuationSubring.ratClosure A ∧
      ¬ ((L₁ : Set A.valuation.Completion) \
        ↑(ValuationSubring.ratClosure A)).Countable ∧
      ¬ ((L₂ : Set A.valuation.Completion) \
        ↑(ValuationSubring.ratClosure A)).Countable :=
  ValuationSubring.exists_two_closed_subfields_completion_inf_eq_ratClosure_of_liesOverPrime
    r A hA

/-- Consequence: the closure of the prime field is a proper subfield of the completion. -/
example (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime r) :
    ValuationSubring.ratClosure A ≠ ⊤ := by
  intro h
  obtain ⟨L₁, -, -, -, -, -, -, h₁, -⟩ :=
    ValuationSubring.exists_two_closed_subfields_completion_inf_eq_ratClosure_of_liesOverPrime
      r A hA
  apply h₁
  simp [h]
