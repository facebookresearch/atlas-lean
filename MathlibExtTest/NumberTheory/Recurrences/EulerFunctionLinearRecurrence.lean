/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.EulerFunctionLinearRecurrence

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

end MathlibExtTest.NumberTheory.Recurrences.EulerFunctionLinearRecurrence
