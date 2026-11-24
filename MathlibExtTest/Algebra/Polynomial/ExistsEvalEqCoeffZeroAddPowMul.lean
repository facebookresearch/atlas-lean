/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.ExistsEvalEqCoeffZeroAddPowMul

/-! # Consumers for the uniform denominator-divisibility evaluation bound -/

namespace PolynomialExistsEvalEqCoeffZeroAddPowMulTest

open Polynomial

/-- The exact source statement, with no added hypothesis. -/
public theorem exactSource (p : Polynomial ℚ) (N : ℤ) (hN : N ≠ 0)
    (hden : ∀ k : ℕ, ∀ q : ℕ, q.Prime → q ∣ (p.coeff k).den → (q : ℤ) ∣ N) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ m : ℤ, ∃ z : ℤ,
      p.eval ((N : ℚ) ^ K * m) = p.coeff 0 + (N : ℚ) ^ (K - K₀) * z :=
  Polynomial.exists_eval_eq_coeff_zero_add_pow_mul p N hN hden

/-- The prime-support hypothesis matters: for `p = X / 2` and `N = 1` it
fails at the prime `2`, and the conclusion fails already at `m = 1`,
since `1 / 2` is not an integer multiple of any power of `1`. -/
public example : ¬ ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ m : ℤ, ∃ z : ℤ,
    (Polynomial.C (1 / 2 : ℚ) * Polynomial.X).eval ((1 : ℚ) ^ K * m)
      = (Polynomial.C (1 / 2 : ℚ) * Polynomial.X).coeff 0 + (1 : ℚ) ^ (K - K₀) * z := by
  rintro ⟨K₀, hK⟩
  obtain ⟨z, hz⟩ := hK K₀ le_rfl 1
  simp only [eval_mul, eval_C, eval_X, coeff_C_mul, coeff_X_zero, mul_zero,
    one_pow, mul_one] at hz
  have h2 : ((2 * z : ℤ) : ℚ) = 1 := by push_cast; linarith
  have h3 : 2 * z = 1 := by exact_mod_cast h2
  omega

end PolynomialExistsEvalEqCoeffZeroAddPowMulTest
