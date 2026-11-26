/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SchatunowskyImaginaryQuadraticQuadSchatunowskySetEqIUnion

/-! # Tests for the decomposition of the Schatunowsky set -/

namespace MathlibExtTest.NumberTheory.SchatunowskyImaginaryQuadraticQuadSchatunowskySetEqIUnion

open NumberField MetaMathlibExt

-- With `n₀ = 0` the union is empty, so the Schatunowsky set is empty.
example {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (hK1 : classNumber K = 1) (ℓ : ℕ)
    (hn₀ : ∀ n ≥ 0, quadPrimeNorm K (n + 1) ^ (ℓ + 1) < quadPrimorialNorm K n) :
    quadSchatunowskySet K ℓ = ∅ := by
  rw [quadSchatunowskySet_eq_iUnion hK hK1 ℓ 0 hn₀]
  have hempty : Finset.Icc 1 0 = (∅ : Finset ℕ) := by decide
  rw [hempty]
  simp

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

end MathlibExtTest.NumberTheory.SchatunowskyImaginaryQuadraticQuadSchatunowskySetEqIUnion
