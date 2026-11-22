/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.InertiaCyclotomic

@[expose] public section

/-- Source-shaped consumer with the original binders. -/
example (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime)
    (hA : A.LiesOverPrime p) (a : (ZMod p)ˣ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 →
      σ μ = μ ^ (a : ZMod p).val :=
  ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow A hp hA a

/-- The conclusion at `μ = 1` is the fixed point forced by any such
inertia element. -/
example (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime)
    (hA : A.LiesOverPrime p) (a : (ZMod p)ˣ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, σ (1 : AlgebraicClosure ℚ) = 1 := by
  obtain ⟨σ, hσ, h⟩ := ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow A hp hA a
  exact ⟨σ, hσ, by rw [h 1 (one_pow p), one_pow]⟩
