/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.FrobeniusExists

@[expose] public section

/-- Source-shaped consumer: the original binders, in the original order. -/
example {q : ℕ} (hq : q.Prime) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime q) :
    ∃ φ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), A.IsFrobeniusAt φ q :=
  ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hq A hA

/-- Source-shaped consumer: the original binders, in the original order. -/
example (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ ∧
      ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ :=
  ValuationSubring.exists_isFrobeniusAt_rat ℓ hℓ

/-- Concrete instance: at the prime `2` some place has a Frobenius element in
its decomposition subgroup. -/
example : ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 2 ∧
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ := by
  obtain ⟨A, hA, σ, hσ⟩ := ValuationSubring.exists_isFrobeniusAt_rat 2 Nat.prime_two
  exact ⟨A, hA, σ, hσ.mem_decompositionSubgroup⟩
