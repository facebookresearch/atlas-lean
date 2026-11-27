/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.InertiaRootsOfUnity

@[expose] public section

-- `exactSource` consumer, with the original binders.
example {q : ℕ} (hq : q.Prime) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime q)
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)}
    (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {n : ℕ} (hn : ¬ q ∣ n)
    {ζ : AlgebraicClosure ℚ} (hζ : ζ ^ n = 1) : σ ζ = ζ :=
  ValuationSubring.apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn
    hq A hA hσ hn hζ

-- Generic consumer over arbitrary fields.
example {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.inertiaSubgroupIn K) {n : ℕ} (hn0 : n ≠ 0)
    (hnA : (n : L) ∉ A.nonunits) {ζ : L} (hζ : ζ ^ n = 1) : σ ζ = ζ :=
  ValuationSubring.apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn_of_not_mem_nonunits
    hσ hn0 hnA hζ

-- The identity automorphism, which lies in every inertia subgroup, fixes a
-- root of unity without using the order hypothesis.
example {q : ℕ} (hq : q.Prime) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime q) {n : ℕ} (hn : ¬ q ∣ n)
    {ζ : AlgebraicClosure ℚ} (hζ : ζ ^ n = 1) :
    (1 : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) ζ = ζ :=
  ValuationSubring.apply_eq_self_of_pow_eq_one_of_mem_inertiaSubgroupIn
    hq A hA (Subgroup.one_mem _) hn hζ

-- Boundary: the root `1`, of order dividing every `n`, is fixed by every
-- automorphism, so the conclusion is sharp only for nontrivial roots.
example {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} :
    σ (1 : AlgebraicClosure ℚ) = 1 :=
  map_one σ
