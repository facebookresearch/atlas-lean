/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Sieve.BrunSieve
import MathlibExt.NumberTheory.Sieve.Rankin
import MathlibExt.NumberTheory.PrimeCounting.Mertens

/-!
# Tests for Brun's truncated Möbius function
-/

@[expose] public section

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega

/-! ### Concrete values of `μ_r` -/

example : brunMoebius 1 6 = 0 := by decide +kernel
example : brunMoebius 2 6 = 1 := by decide +kernel
example : brunMoebius 1 5 = -1 := by decide +kernel
example : brunMoebius 2 30 = 0 := by decide +kernel
example : brunMoebius 3 30 = -1 := by decide +kernel
-- Non-squarefree arguments still give `0`, whatever the truncation level.
example : brunMoebius 5 4 = 0 := by decide +kernel

/-! ### Boundary values -/

example (r : ℕ) : brunMoebius r 0 = 0 := by simp
example (r : ℕ) : brunMoebius r 1 = 1 := by simp [brunMoebius_apply]
-- `μ_0 = δ`: only `d = 1` survives.
example : brunMoebius 0 2 = 0 := by decide +kernel
-- Once `r ≥ ω(d)`, `μ_r(d) = μ(d)`.
example (d : ℕ) (hd : ω d ≤ 3) : brunMoebius 3 d = μ d := by simp [brunMoebius_apply, hd]

/-! ### Concrete values of `ψ_r = μ_r * ζ` -/

example : brunPsi 1 6 = -1 := by decide +kernel
example : brunPsi 1 30 = -2 := by decide +kernel
example : brunPsi 2 30 = 1 := by decide +kernel
-- Full truncation level: `ψ_r(n) = ∑_{d ∣ n} μ(d) = 0` for `n > 1` once `r ≥ ω(n)`.
example : brunPsi 3 30 = 0 := by decide +kernel
example (r : ℕ) : brunPsi r 1 = 1 := brunPsi_one r
example (r : ℕ) : brunPsi r 0 = 0 := by simp

/-! ### Agreement with the truncation identity -/

example : brunPsi 1 30 = (-1) ^ 1 * ((ω 30 - 1).choose 1 : ℤ) :=
  brunPsi_eq_neg_one_pow_mul_choose (by norm_num) 1
example : (ω 30 - 1).choose 1 = 2 := by decide +kernel
-- `ψ_0(n) = 1` for every `n ≥ 1`.
example {n : ℕ} (hn : 2 ≤ n) : brunPsi 0 n = 1 := by
  simp [brunPsi_eq_neg_one_pow_mul_choose hn]

/-! ### Helper lemmas -/

example : μ (2 * 3 * 5) = -1 := by
  have := moebius_prod_of_prime (s := {2, 3, 5}) (by decide)
  simpa using this
example : ω (2 * 3 * 7) = 3 := by
  have := cardDistinctFactors_prod_of_prime (s := {2, 3, 7}) (by decide)
  simpa using this

/-! ### The remainder bound has satisfiable hypotheses

With all primes sifted and `ω ≡ 1`, the hypothesis on `∑ ω(p)/p` is Mertens' second
theorem. -/

example : ∃ c₄ K : ℝ, ∀ z : ℝ, 3 ≤ z → ∀ r : ℕ,
    |∑ δ ∈ (Nat.siftingPrimorial (fun _ => True) ⌊z⌋₊).divisors with 1 < δ,
        (brunPsi r δ : ℝ) * (∏ _p ∈ δ.primeFactors, (1 : ℝ)) /
          ∏ p ∈ δ.primeFactors, ((p : ℝ) - 1)| ≤
      K * (1 * Real.log (Real.log z) + c₄) ^ r / r.factorial * Real.log z ^ (1 : ℝ) := by
  obtain ⟨C, hC⟩ := Chebyshev.abs_sum_primesLE_inv_sub_log_log_le
  refine abs_sum_brunPsi_mul_div_le (fun _ => True) (fun _ => 1) 1 1 C (fun _ => zero_le_one)
    (fun _p _ hp => by exact_mod_cast hp.one_lt) (fun _ => le_rfl) fun z hz => ?_
  have h := (abs_le.mp (hC z (by linarith))).2
  simp only [one_div, one_mul, Finset.filter_true]
  linarith
