/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Fib.Basic

/-!
# Fibonacci numbers and `π²`

Statements from Joseph Tonien, *Fibonacci and Pi Squared*, The Fibonacci Quarterly 62 (2024),
no. 1 (paper `tonien10292023`), read from the extracted text layer (the primary PDF is not
reachable for agents).

The paper's sequences are pinned by hypotheses rather than new definitions: `p n` is the
polynomial sequence with `p 1 = 1` and
`p (n + 1) = (2X + 2n + 1)(2X + 2n + 2) p n - (X + 1)² p n (X + 1)` for `n ≥ 1` (the value `p 0`
is unused); `a` is the real Fibonacci-type sequence with `a 0 = -8√5 / 250`,
`a 1 = (25 - 4√5) / 250`; `b` has `b 0 = b 1 = 0` and
`b (n + 1) = b n + b (n - 1) + (-1)^(n+1) p n (0) / (2n)!` for `n ≥ 1`. In each display the second
identity is the continuation line `= …` of the aligned display that starts with `π² =`; the
text layer drops the repeated left side.
-/

open Polynomial

namespace MetaMathlibExt

@[expose] public section

/-- Theorem 2.1: for every `n ≥ 1`,
`π² = (b_(n-1) + (-1)ⁿ Σ_k (k!)² p_n(k) F_(2k+2) / (2k+2n)!) / a_(n-1)` (2.1) and
`π² = (b_n + (-1)^(n+1) Σ_k (k!)² p_n(k) F_(2k+1) / (2k+2n)!) / a_n` (2.2).

Source: Joseph Tonien, *Fibonacci and Pi Squared*, The Fibonacci Quarterly 62 (2024), no. 1,
Theorem 2.1 (`fq-2024-tonien10292023-thm-2.1`). -/
public theorem_wanted pi_sq_eq_fibonacci_factorial_series (p : ℕ → ℤ[X]) (hp1 : p 1 = 1)
    (hp : ∀ n, 1 ≤ n → p (n + 1) = (2 * X + C (2 * n + 1 : ℤ)) * (2 * X + C (2 * n + 2 : ℤ)) *
      p n - (X + 1) ^ 2 * (p n).comp (X + 1))
    (a : ℕ → ℝ) (ha0 : a 0 = -(8 * √5) / 250) (ha1 : a 1 = (25 - 4 * √5) / 250)
    (ha : ∀ n, 1 ≤ n → a (n + 1) = a n + a (n - 1))
    (b : ℕ → ℝ) (hb0 : b 0 = 0) (hb1 : b 1 = 0)
    (hb : ∀ n, 1 ≤ n → b (n + 1) =
      b n + b (n - 1) + (-1) ^ (n + 1) * (((p n).eval 0 : ℤ) : ℝ) / ((2 * n).factorial : ℝ))
    {n : ℕ} (hn : 1 ≤ n) :
    Real.pi ^ 2 = (b (n - 1) + (-1) ^ n * ∑' k : ℕ, ((k.factorial ^ 2 : ℕ) : ℝ) *
        (((p n).eval (k : ℤ) : ℤ) : ℝ) * (Nat.fib (2 * k + 2) : ℝ) /
          ((2 * k + 2 * n).factorial : ℝ)) / a (n - 1) ∧
      Real.pi ^ 2 = (b n + (-1) ^ (n + 1) * ∑' k : ℕ, ((k.factorial ^ 2 : ℕ) : ℝ) *
        (((p n).eval (k : ℤ) : ℤ) : ℝ) * (Nat.fib (2 * k + 1) : ℝ) /
          ((2 * k + 2 * n).factorial : ℝ)) / a n

/-- Lemma 2.2 (the case `n = 1`):
`π² = (250 / (8√5)) Σ_k (k!)² F_(2k+2) / (2k+2)!` (2.3) and
`π² = (250 / (25 - 4√5)) Σ_k (k!)² F_(2k+1) / (2k+2)!` (2.4).

Source: Joseph Tonien, *Fibonacci and Pi Squared*, The Fibonacci Quarterly 62 (2024), no. 1,
Lemma 2.2 (`fq-2024-tonien10292023-lem-2.2`). -/
public theorem_wanted pi_sq_eq_fibonacci_central_series :
    Real.pi ^ 2 = 250 / (8 * √5) * ∑' k : ℕ, ((k.factorial ^ 2 : ℕ) : ℝ) *
        (Nat.fib (2 * k + 2) : ℝ) / ((2 * k + 2).factorial : ℝ) ∧
      Real.pi ^ 2 = 250 / (25 - 4 * √5) * ∑' k : ℕ, ((k.factorial ^ 2 : ℕ) : ℝ) *
        (Nat.fib (2 * k + 1) : ℝ) / ((2 * k + 2).factorial : ℝ)

/-- Lemma 2.3: `a_n = ((25 - 4√5) / 250) F_n - (8√5 / 250) F_(n-1)`, stated for `n ≥ 1`; the case
`n = 0` with the paper's convention `F_(-1) = 1` is the initial value `a 0 = -8√5 / 250`.

Source: Joseph Tonien, *Fibonacci and Pi Squared*, The Fibonacci Quarterly 62 (2024), no. 1,
Lemma 2.3 (`fq-2024-tonien10292023-lem-2.3`). -/
public theorem_wanted fibPiSquared_coeff_eq_fib (a : ℕ → ℝ) (ha0 : a 0 = -(8 * √5) / 250)
    (ha1 : a 1 = (25 - 4 * √5) / 250) (ha : ∀ n, 1 ≤ n → a (n + 1) = a n + a (n - 1)) (n : ℕ) :
    a (n + 1) = (25 - 4 * √5) / 250 * Nat.fib (n + 1) - 8 * √5 / 250 * Nat.fib n

/-- Lemma 2.4: for `n ≥ 1`,
`p_n(x) = Σ_(j=0)^(n-1) (-1)^j C(n-1, j) Π_(k=2j+3)^(2n) (2x + k) Π_(t=1)^j (x + t)²`.

Source: Joseph Tonien, *Fibonacci and Pi Squared*, The Fibonacci Quarterly 62 (2024), no. 1,
Lemma 2.4 (`fq-2024-tonien10292023-lem-2.4`). -/
public theorem_wanted fibPiSquared_poly_eq_sum (p : ℕ → ℤ[X]) (hp1 : p 1 = 1)
    (hp : ∀ n, 1 ≤ n → p (n + 1) = (2 * X + C (2 * n + 1 : ℤ)) * (2 * X + C (2 * n + 2 : ℤ)) *
      p n - (X + 1) ^ 2 * (p n).comp (X + 1))
    {n : ℕ} (hn : 1 ≤ n) :
    p n = ∑ j ∈ Finset.range n, (-1) ^ j * ((n - 1).choose j : ℤ[X]) *
      (∏ k ∈ Finset.Ico (2 * j + 3) (2 * n + 1), (2 * X + C (k : ℤ))) *
      ∏ t ∈ Finset.Icc 1 j, (X + C (t : ℤ)) ^ 2

end

end MetaMathlibExt
