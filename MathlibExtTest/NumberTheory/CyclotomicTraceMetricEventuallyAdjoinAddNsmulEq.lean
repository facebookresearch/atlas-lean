/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CyclotomicTraceMetricEventuallyAdjoinAddNsmulEq

/-! # Tests for primitive elements `α + nβ` in a prime cyclotomic field -/

namespace MathlibExtTest.NumberTheory.CyclotomicTraceMetricEventuallyAdjoinAddNsmulEq

open MetaMathlibExt

example {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {3} ℚ K] (α β : K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      IntermediateField.adjoin ℚ {α + (n : K) * β} =
        IntermediateField.adjoin ℚ {α, β} :=
  eventually_adjoin_add_nsmul_eq Nat.prime_three α β

example {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {3} ℚ K] (α β : K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      α ∈ IntermediateField.adjoin ℚ {α + (n : K) * β} ∧
        β ∈ IntermediateField.adjoin ℚ {α + (n : K) * β} := by
  obtain ⟨n₀, hn₀⟩ := eventually_adjoin_add_nsmul_eq Nat.prime_three α β
  refine ⟨n₀, fun n hn => ?_⟩
  rw [hn₀ n hn]
  exact ⟨IntermediateField.subset_adjoin ℚ _ (by simp),
    IntermediateField.subset_adjoin ℚ _ (by simp)⟩

end MathlibExtTest.NumberTheory.CyclotomicTraceMetricEventuallyAdjoinAddNsmulEq
