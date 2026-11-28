/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.LandauFormula
import MathlibExt.NumberTheory.LSeries.RiemannXiZeros

/-!
# Tests for Landau's formula

`(1/T) ∑_{|γ| ≤ T} n^ρ → -Λ(n)/π`, instantiated at an actual enumeration of the zeros and at
`n = 2` (a prime, limit `-log 2 / π`) and `n = 6` (not a prime power, limit `0`).
-/

@[expose] public section

open Filter Topology RiemannXi ArithmeticFunction

namespace LandauFormulaTest

example : ∃ (ι : Type) (z : ι → ℂ), Tendsto (fun T : ℝ => (1 / (T : ℂ)) *
    ∑' k, (if |(z k).im| ≤ T then ((2 : ℕ) : ℂ) ^ z k else 0)) atTop
      (𝓝 (-(Real.log 2 : ℂ) / (Real.pi : ℂ))) := by
  obtain ⟨ι, z, hz⟩ := exists_card_eq_analyticOrderAt
  refine ⟨ι, z, ?_⟩
  have h := tendsto_one_div_mul_tsum_natCast_cpow_zeros z hz (n := 2) (by norm_num)
  rwa [vonMangoldt_apply_prime Nat.prime_two] at h

example : ∃ (ι : Type) (z : ι → ℂ), Tendsto (fun T : ℝ => (1 / (T : ℂ)) *
    ∑' k, (if |(z k).im| ≤ T then ((6 : ℕ) : ℂ) ^ z k else 0)) atTop (𝓝 0) := by
  obtain ⟨ι, z, hz⟩ := exists_card_eq_analyticOrderAt
  refine ⟨ι, z, ?_⟩
  have h := tendsto_one_div_mul_tsum_natCast_cpow_zeros z hz (n := 6) (by norm_num)
  have h6 : ¬ IsPrimePow 6 := by decide
  rwa [vonMangoldt_eq_zero_iff.mpr h6, Complex.ofReal_zero, neg_zero, zero_div] at h

end LandauFormulaTest
