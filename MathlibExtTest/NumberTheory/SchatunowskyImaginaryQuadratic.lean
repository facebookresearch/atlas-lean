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

-- The proved statement, restated verbatim, is the one in the proved module.
private theorem quadSchatunowskySet_norm_bound_and_finite_restated {K : Type*} [Field K]
    [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (hK1 : classNumber K = 1) (ℓ n₀ : ℕ)
    (hn₀ : ∀ n ≥ n₀, quadPrimeNorm K (n + 1) ^ (ℓ + 1) < quadPrimorialNorm K n) :
    (∀ α : 𝓞 K, quadPrimeNorm K n₀ ^ (ℓ + 1) < Ideal.absNorm (Ideal.span {α}) →
        α ∉ quadSchatunowskySet K ℓ) ∧
      (quadSchatunowskySet K ℓ).Finite :=
  quadSchatunowskySet_norm_bound_and_finite hK hK1 ℓ n₀ hn₀

-- Reverse inclusion at an admissible cutoff: an element at the upper endpoint of the `n`-th
-- interval that lies in every nonzero prime ideal of norm at most `N(π_{n-1})` belongs to the
-- Schatunowsky set.
example {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (hK1 : classNumber K = 1) (ℓ n₀ n : ℕ)
    (hn₀ : ∀ n ≥ n₀, quadPrimeNorm K (n + 1) ^ (ℓ + 1) < quadPrimorialNorm K n)
    (hn : n ∈ Finset.Icc 1 n₀) {α : 𝓞 K}
    (hlow : quadPrimeNorm K (n - 1) ^ (ℓ + 1) < Ideal.absNorm (Ideal.span {α}))
    (hup : Ideal.absNorm (Ideal.span {α}) = quadPrimeNorm K n ^ (ℓ + 1))
    (hsmall : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ →
      Ideal.absNorm P ≤ quadPrimeNorm K (n - 1) → α ∈ P) :
    α ∈ quadSchatunowskySet K ℓ := by
  rw [quadSchatunowskySet_eq_iUnion hK hK1 ℓ n₀ hn₀]
  exact Set.mem_iUnion₂_of_mem hn ⟨hlow, hup.le, hsmall⟩

-- First interval at an admissible cutoff `n₀ ≥ 1`: every element with
-- `1 < N(α) ≤ N(π₁)^(ℓ+1)` belongs, since no nonzero prime ideal has norm at most `1`.
example {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (hK1 : classNumber K = 1) (ℓ n₀ : ℕ)
    (hn₀ : ∀ n ≥ n₀, quadPrimeNorm K (n + 1) ^ (ℓ + 1) < quadPrimorialNorm K n)
    (h1 : 1 ≤ n₀) {α : 𝓞 K} (hlow : 1 < Ideal.absNorm (Ideal.span {α}))
    (hup : Ideal.absNorm (Ideal.span {α}) ≤ quadPrimeNorm K 1 ^ (ℓ + 1)) :
    α ∈ quadSchatunowskySet K ℓ := by
  rw [quadSchatunowskySet_eq_iUnion hK hK1 ℓ n₀ hn₀]
  refine Set.mem_iUnion₂_of_mem (Finset.mem_Icc.mpr ⟨le_rfl, h1⟩) ⟨?_, hup, ?_⟩
  · simpa [quadPrimeNorm_zero] using hlow
  · intro P hP hbot hle
    simp only [Nat.sub_self, quadPrimeNorm_zero] at hle
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
    · exact absurd (Ideal.absNorm_eq_zero_iff.mp h) hbot
    · exact absurd (Ideal.absNorm_eq_one_iff.mp h) hP.ne_top

-- Membership in the Schatunowsky set gives norm bounds at some index.
example {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (hK1 : classNumber K = 1) (ℓ n₀ : ℕ)
    (hn₀ : ∀ n ≥ n₀, quadPrimeNorm K (n + 1) ^ (ℓ + 1) < quadPrimorialNorm K n)
    {α : 𝓞 K} (hα : α ∈ quadSchatunowskySet K ℓ) :
    ∃ n ∈ Finset.Icc 1 n₀, quadPrimeNorm K (n - 1) ^ (ℓ + 1) < Ideal.absNorm (Ideal.span {α}) ∧
      Ideal.absNorm (Ideal.span {α}) ≤ quadPrimeNorm K n ^ (ℓ + 1) := by
  rw [quadSchatunowskySet_eq_iUnion hK hK1 ℓ n₀ hn₀] at hα
  obtain ⟨n, hn, hlow, hup, -⟩ := Set.mem_iUnion₂.mp hα
  exact ⟨n, hn, hlow, hup⟩

-- Large elements lie in every nonzero prime ideal of small norm.
example {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (hK1 : classNumber K = 1) (ℓ n : ℕ)
    {α : 𝓞 K} (hα : α ∈ quadSchatunowskySet K ℓ)
    (hn : quadPrimeNorm K n ^ (ℓ + 1) < Ideal.absNorm (Ideal.span {α}))
    {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hbot : P ≠ ⊥) (hle : Ideal.absNorm P ≤ quadPrimeNorm K n) :
    α ∈ P :=
  mem_prime_of_mem_quadSchatunowskySet hK hK1 ℓ n α hα hn P hP hbot hle

end MathlibExtTest.SchatunowskyImaginaryQuadratic
