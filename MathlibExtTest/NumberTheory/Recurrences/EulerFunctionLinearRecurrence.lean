/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.EulerFunctionLinearRecurrence
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.NumberTheory.Recurrences.EulerFunctionLinearRecurrence

example : ArithmeticFunction.cardFactors (2 ^ 12) = 12 := by
  exact ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_two

example : ∃ C : ℝ, ∀ N : ℕ, 10 ≤ N →
    ((Finset.Icc 1 N).filter (fun n =>
      10 * Real.log (Real.log N) ≤ (ArithmeticFunction.cardFactors n : ℝ))).card ≤
        C * (N : ℝ) / Real.log N ^ 2 := by
  obtain ⟨C, hC⟩ := MetaMathlibExt.card_cardFactors_ge_ten_log_log_le
  refine ⟨C, fun N hN => ?_⟩
  simpa only [Nat.floor_natCast] using hC N (by exact_mod_cast hN)

public theorem totient_bound_three_and_twelve :
    ∃ C : ℝ, 0 < C ∧
      C / Real.log (Real.log (3 : ℕ)) ≤ (2 : ℝ) / 3 ∧
      C / Real.log (Real.log (12 : ℕ)) ≤ (4 : ℝ) / 12 := by
  obtain ⟨C, hC, h⟩ := MetaMathlibExt.totient_div_gg_and_sigma_div_ll_log_log.1
  refine ⟨C, hC, ?_, ?_⟩
  · have ht : Nat.totient 3 = 2 := by decide
    simpa [ht] using h 3 (by norm_num)
  · have ht : Nat.totient 12 = 4 := by decide
    simpa [ht] using h 12 (by norm_num)

public theorem sigma_bound_three_and_twelve :
    ∃ C : ℝ,
      (4 : ℝ) / 3 ≤ C * Real.log (Real.log (3 : ℕ)) ∧
      (28 : ℝ) / 12 ≤ C * Real.log (Real.log (12 : ℕ)) := by
  obtain ⟨C, h⟩ := MetaMathlibExt.totient_div_gg_and_sigma_div_ll_log_log.2
  refine ⟨C, ?_, ?_⟩
  · have hs : ArithmeticFunction.sigma 1 3 = 4 := by decide
    simpa [hs] using h 3 (by norm_num)
  · have hs : ArithmeticFunction.sigma 1 12 = 28 := by decide
    simpa [hs] using h 12 (by norm_num)

end MathlibExtTest.NumberTheory.Recurrences.EulerFunctionLinearRecurrence
