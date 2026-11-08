/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import WantedExt.NumberTheory.GcdSumMomentsWanted

/-!
# Mean square of the error term for moments of the gcd-sum function

Statements from Isao Kiuchi and Yuki Tsuruta, *Mean Square Estimates for GCD-Sum Functions*,
INTEGERS 25 (2025), Article A53. With `A(n) = (1/n) ∑_{m=1}^n gcd(m, n)` (`gcdSumMean`), the
paper writes `∑_{n ≤ x} A(n)^k = x Q_{2^k - 1}(log x) + E_k(x)` (Zhang and Zhai) and studies
`I_k(T) = ∫_1^T E_k(u)^2 du` and `J_k(T) = ∫_1^T E_k(u) du` under the Riemann Hypothesis.

The statements below assert the existence of a real polynomial `P` for which the error term
`E(u) = ∑_{n ≤ u} A(n)^k - u P(log u)` satisfies the bound. Either bound forces
`E(u) = o(u)` on average, so such a `P` is unique and is the paper's `Q_{2^k - 1}`; the existential
form loses nothing. The paper's range `η_k ≤ (1/2^{k+1}) log log T - 1` is equivalent to its
condition `T ≥ exp(exp(2^{k+1}(η_k + 1)))`; for a fixed `η_k` both hold for all large `T`, so they
are absorbed into the threshold `T₀`.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- **Mean square of `E_k` under RH**: assume the Riemann Hypothesis and let `k ≥ 2`. For every
fixed `η` with `(1/2^k)(4^k - 3^k - C(2^k, 2)) + 1/2^{k+1} + 1 ≤ η` and all sufficiently large `T`,
`I_k(T) = ∫_1^T E_k(u)^2 du ≪ T^{2 - 1/2^k} exp(2 η log T / log log T)`.

Source: Isao Kiuchi and Yuki Tsuruta, *Mean Square Estimates for GCD-Sum Functions*, INTEGERS 25
(2025), Article A53, Theorem 1 (`integers-2025-A53-thm-1`). -/
public theorem_wanted gcdSumMean_pow_error_sq_integral_le (hRH : RiemannHypothesis) (k : ℕ)
    (hk : 2 ≤ k) :
    ∃ P : ℝ[X], ∀ η : ℝ,
      ((4 : ℝ) ^ k - 3 ^ k - ((2 ^ k).choose 2 : ℕ)) / 2 ^ k + 1 / 2 ^ (k + 1) + 1 ≤ η →
      ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
        ∫ u in (1 : ℝ)..T,
            (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, gcdSumMean n ^ k - u * P.eval (Real.log u)) ^ 2 ≤
          C * T ^ (2 - 1 / (2 : ℝ) ^ k) *
            Real.exp (2 * η * Real.log T / Real.log (Real.log T))

/-- **Integral of `E_k` under RH**: under the hypotheses of Theorem 1 (RH, `k ≥ 2`, a fixed `η`
with `(1/2^k)(4^k - 3^k - C(2^k, 2)) + 1/2^{k+1} + 1 ≤ η`), for all sufficiently large `T`,
`J_k(T) = ∫_1^T E_k(u) du ≪ T^{3/2 - 1/2^{k+1}} exp(η log T / log log T)` (stated for `|J_k(T)|`).

Source: Isao Kiuchi and Yuki Tsuruta, *Mean Square Estimates for GCD-Sum Functions*, INTEGERS 25
(2025), Article A53, Corollary 1 (`integers-2025-A53-cor-1`). -/
public theorem_wanted gcdSumMean_pow_error_integral_le (hRH : RiemannHypothesis) (k : ℕ)
    (hk : 2 ≤ k) :
    ∃ P : ℝ[X], ∀ η : ℝ,
      ((4 : ℝ) ^ k - 3 ^ k - ((2 ^ k).choose 2 : ℕ)) / 2 ^ k + 1 / 2 ^ (k + 1) + 1 ≤ η →
      ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
        |∫ u in (1 : ℝ)..T,
            (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, gcdSumMean n ^ k - u * P.eval (Real.log u))| ≤
          C * T ^ (3 / 2 - 1 / (2 : ℝ) ^ (k + 1)) *
            Real.exp (η * Real.log T / Real.log (Real.log T))

end

end MetaMathlibExt
