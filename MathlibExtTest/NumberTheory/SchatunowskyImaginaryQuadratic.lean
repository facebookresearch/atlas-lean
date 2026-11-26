/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SchatunowskyImaginaryQuadratic

/-! # Tests for prime norms, primorial norms and Schatunowsky sets -/

namespace MathlibExtTest.SchatunowskyImaginaryQuadratic

open NumberField MetaMathlibExt

-- The zeroth prime and primorial norms are one.
example (K : Type*) [Field K] [NumberField K] :
    quadPrimeNorm K 0 = 1 ∧ quadPrimorialNorm K 0 = 1 :=
  ⟨quadPrimeNorm_zero K, quadPrimorialNorm_zero K⟩

-- One is not in any Schatunowsky set.
example (K : Type*) [Field K] [NumberField K] (ℓ : ℕ) :
    (1 : 𝓞 K) ∉ quadSchatunowskySet K ℓ :=
  one_not_mem_quadSchatunowskySet K ℓ

-- Membership in a Schatunowsky set implies the norm exceeds one.
example {K : Type*} [Field K] [NumberField K] {ℓ : ℕ} {α : 𝓞 K}
    (hα : α ∈ quadSchatunowskySet K ℓ) :
    1 < Ideal.absNorm (Ideal.span {α}) :=
  hα.1

-- Check the published API from the proved module alone.
example {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (hK1 : classNumber K = 1) (ℓ n : ℕ)
    (α : 𝓞 K) (hα : α ∈ quadSchatunowskySet K ℓ)
    (hn : quadPrimeNorm K n ^ (ℓ + 1) < Ideal.absNorm (Ideal.span {α})) :
    ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → Ideal.absNorm P ≤ quadPrimeNorm K n → α ∈ P :=
  mem_prime_of_mem_quadSchatunowskySet hK hK1 ℓ n α hα hn

-- The cutoff includes ideals of norm exactly `quadPrimeNorm K n`, even when `ℓ = 0`.
example {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (hK1 : classNumber K = 1) (n : ℕ)
    (α : 𝓞 K) (hα : α ∈ quadSchatunowskySet K 0)
    (hn : quadPrimeNorm K n < Ideal.absNorm (Ideal.span {α}))
    (P : Ideal (𝓞 K)) (hP : P.IsPrime) (hPbot : P ≠ ⊥)
    (hPnorm : Ideal.absNorm P = quadPrimeNorm K n) : α ∈ P :=
  mem_prime_of_mem_quadSchatunowskySet hK hK1 0 n α hα
    (by simpa only [Nat.zero_add, pow_one] using hn) P hP hPbot hPnorm.le

-- The proved statement, restated verbatim, is the one in the proved module.
private theorem quadSchatunowskySet_norm_bound_and_finite_restated {K : Type*} [Field K]
    [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (hK1 : classNumber K = 1) (ℓ n₀ : ℕ)
    (hn₀ : ∀ n ≥ n₀, quadPrimeNorm K (n + 1) ^ (ℓ + 1) < quadPrimorialNorm K n) :
    (∀ α : 𝓞 K, quadPrimeNorm K n₀ ^ (ℓ + 1) < Ideal.absNorm (Ideal.span {α}) →
        α ∉ quadSchatunowskySet K ℓ) ∧
      (quadSchatunowskySet K ℓ).Finite :=
  quadSchatunowskySet_norm_bound_and_finite hK hK1 ℓ n₀ hn₀

end MathlibExtTest.SchatunowskyImaginaryQuadratic
