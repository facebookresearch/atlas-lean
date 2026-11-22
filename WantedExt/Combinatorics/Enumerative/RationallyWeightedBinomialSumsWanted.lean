/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.Harmonic.Defs
public import MathlibExt.Combinatorics.Enumerative.HsuShiueGeneralizedStirlingNumber
public import MathlibExt.NumberTheory.LucasSequence
import MathlibExt.Combinatorics.Enumerative.StirlingSecondExplicit

/-!
# Rationally weighted binomial sums via differential and integral operators

Statements from Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation
of Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), no. 1, 45–56.

`{r, i}` is `Nat.stirlingSecond r i`, `(N)_i` is the falling factorial `N.descFactorial i`, and the
rising factorial `(k + 1)^{(s)} = (k + 1)(k + 2) ⋯ (k + s)` is `(k + 1).ascFactorial s`. A
polynomial `f(x) = ∑_{k=0}^N a_k x^k` is written `∑ k ∈ range (N + 1), C (a k) * X ^ k`, and its
`i`-th derivative is `derivative^[i]`. `F_n` and `L_n` are `Nat.fib n` and `lucasNumber n`.
-/

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- Scherk's identity: for `f(x) = ∑_{k=0}^N a_k x^k` with real coefficients,
`∑_{k=0}^N k^r a_k x^k = ∑_{i=0}^r {r, i} x^i f^{(i)}(x)`.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 2.1, equation (2.1). -/
public theorem_wanted sum_pow_mul_coeff_eq_sum_stirlingSecond_derivative (a : ℕ → ℝ) (N r : ℕ)
    (x : ℝ) :
    ∑ k ∈ Finset.range (N + 1), (k : ℝ) ^ r * a k * x ^ k =
      ∑ i ∈ Finset.range (r + 1), (Nat.stirlingSecond r i : ℝ) * x ^ i *
        (derivative^[i] (∑ k ∈ Finset.range (N + 1), C (a k) * X ^ k)).eval x

/-- For real `s`, `x > 0` and `f(x) = ∑_{k=0}^N a_k x^k`,
`∑_{k=0}^N (k)^{(s,r)} a_k x^{k+rs} = ∑_{i=0}^r {r, i}_s x^{rs+i} f^{(i)}(x)`, where
`(k)^{(s,r)} = k (k + s) ⋯ (k + (r - 1) s)` and the paper's `s`-Stirling numbers of the second
kind `{r, i}_s` (recurrence `{r+1, k}_s = (rs + k) {r, k}_s + {r, k-1}_s`, `{0, 0}_s = 1`,
`{r, 0}_s = 0` for `r ≥ 1`) are the Hsu–Shiue numbers `S(r, i; -s, 1, 0)`. The real powers
`x^{k+rs}` are `Real.rpow`, so `x > 0` is added.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 2.1, equation (2.2). -/
public theorem_wanted sum_risingStep_mul_coeff_eq_sum_hsuShiue_derivative (s : ℝ)
    (S : ℕ → ℕ → ℝ) (hS : IsHsuShiueFamily S (-s) 1 0) (a : ℕ → ℝ) (N r : ℕ) (x : ℝ)
    (hx : 0 < x) :
    ∑ k ∈ Finset.range (N + 1),
        (∏ j ∈ Finset.range r, ((k : ℝ) + j * s)) * a k * x ^ ((k : ℝ) + r * s) =
      ∑ i ∈ Finset.range (r + 1), S r i * x ^ ((r : ℝ) * s + i) *
        (derivative^[i] (∑ k ∈ Finset.range (N + 1), C (a k) * X ^ k)).eval x

/-- `{r, 3} = (3^{r-1} + 1)/2 - 2^{r-1}`, stated for `r ≥ 1` (the paper says `r ≥ 3`; both
sides vanish at `r = 1, 2`). Proved from `stirlingSecond_mul_factorial_eq_sum` at `k = 3`.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Proposition 2.2. -/
public theorem stirlingSecond_three_eq (r : ℕ) (hr : 1 ≤ r) :
    (Nat.stirlingSecond r 3 : ℚ) = (3 ^ (r - 1) + 1) / 2 - 2 ^ (r - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hr
  have h := stirlingSecond_mul_factorial_eq_sum (1 + m) 3
  simp [Finset.sum_range_succ, Nat.factorial, pow_add] at h
  have hR : ((Nat.stirlingSecond (1 + m) 3 : ℚ) : ℝ) = (((3 ^ m + 1) / 2 - 2 ^ m : ℚ) : ℝ) := by
    push_cast
    linear_combination h / 6
  rw [Nat.add_sub_cancel_left]
  exact_mod_cast hR

/-- Greenstreet's identity: `∑_{k=1}^N (-1)^k binom(N, k) 2^{N-k} k² = N² - 2N`.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 2.3. -/
public theorem_wanted sum_neg_one_pow_choose_two_pow_mul_sq (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (-1 : ℤ) ^ k * (N.choose k : ℤ) * 2 ^ (N - k) * (k : ℤ) ^ 2 =
      (N : ℤ) ^ 2 - 2 * N

/-- For `h(x) = ∑_{r=0}^t A_r x^r ∈ ℂ[x]` and `F(x) = ∑_{i=0}^N F_i x^i`,
`∑_{k=0}^N h(k) F_k x^k = ∑_{r=0}^t A_r ∑_{i=0}^r {r, i} x^i F^{(i)}(x)` for `x ∈ ℂ`.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 2.4. -/
public theorem_wanted sum_poly_mul_fib_pow_eq_sum_stirlingSecond_derivative (A : ℕ → ℂ)
    (t N : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (N + 1),
        (∑ r ∈ Finset.range (t + 1), A r * (k : ℂ) ^ r) * (Nat.fib k : ℂ) * x ^ k =
      ∑ r ∈ Finset.range (t + 1), A r * ∑ i ∈ Finset.range (r + 1),
        (Nat.stirlingSecond r i : ℂ) * x ^ i *
          (derivative^[i] (∑ j ∈ Finset.range (N + 1), C (Nat.fib j : ℂ) * X ^ j)).eval x

/-- `∑_{k=0}^N k^r binom(N, k) F_k = ∑_{i=0}^r {r, i} (N)_i F_{2N-i}`.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 2.5. -/
public theorem_wanted sum_pow_mul_choose_mul_fib (N r : ℕ) :
    ∑ k ∈ Finset.range (N + 1), k ^ r * N.choose k * Nat.fib k =
      ∑ i ∈ Finset.range (r + 1), Nat.stirlingSecond r i * N.descFactorial i * Nat.fib (2 * N - i)

/-- `∑_{k=0}^N k^r binom(N, k) L_k = ∑_{i=0}^r {r, i} (N)_i L_{2N-i}`.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 2.5. -/
public theorem_wanted sum_pow_mul_choose_mul_lucasNumber (N r : ℕ) :
    ∑ k ∈ Finset.range (N + 1), k ^ r * N.choose k * lucasNumber k =
      ∑ i ∈ Finset.range (r + 1),
        Nat.stirlingSecond r i * N.descFactorial i * lucasNumber (2 * N - i)

/-- For any real sequence `W` with `W_{n+2} = a W_{n+1} + b W_n`,
`∑_{k=0}^N k^r binom(N, k) a^k b^{N-k} W_k = ∑_{i=0}^r {r, i} (N)_i a^i W_{2N-i}`.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 2.5. -/
public theorem_wanted sum_pow_mul_choose_mul_secondOrder (a b : ℝ) (W : ℕ → ℝ)
    (hW : ∀ n, W (n + 2) = a * W (n + 1) + b * W n) (N r : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (k : ℝ) ^ r * N.choose k * a ^ k * b ^ (N - k) * W k =
      ∑ i ∈ Finset.range (r + 1),
        (Nat.stirlingSecond r i : ℝ) * N.descFactorial i * a ^ i * W (2 * N - i)

/-- The cases `r = 1, 2, 3, 4` of Theorem 2.5 for `F_k`:
`∑ k binom(N,k) F_k = N F_{2N-1}`, `∑ k² binom(N,k) F_k = N F_{2N-1} + N(N-1) F_{2N-2}`,
`∑ k³ binom(N,k) F_k = N F_{2N-1} + 3N(N-1) F_{2N-2} + N(N-1)(N-2) F_{2N-3}`, and
`∑ k⁴ binom(N,k) F_k = N F_{2N-1} + 7N(N-1) F_{2N-2} + 6N(N-1)(N-2) F_{2N-3}
+ N(N-1)(N-2)(N-3) F_{2N-4}`, sums over `1 ≤ k ≤ N`.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 2.6. -/
public theorem_wanted sum_pow_mul_choose_mul_fib_small (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, k * N.choose k * Nat.fib k = N * Nat.fib (2 * N - 1)) ∧
    (∑ k ∈ Finset.Icc 1 N, k ^ 2 * N.choose k * Nat.fib k =
      N * Nat.fib (2 * N - 1) + N * (N - 1) * Nat.fib (2 * N - 2)) ∧
    (∑ k ∈ Finset.Icc 1 N, k ^ 3 * N.choose k * Nat.fib k =
      N * Nat.fib (2 * N - 1) + 3 * N * (N - 1) * Nat.fib (2 * N - 2) +
        N * (N - 1) * (N - 2) * Nat.fib (2 * N - 3)) ∧
    ∑ k ∈ Finset.Icc 1 N, k ^ 4 * N.choose k * Nat.fib k =
      N * Nat.fib (2 * N - 1) + 7 * N * (N - 1) * Nat.fib (2 * N - 2) +
        6 * N * (N - 1) * (N - 2) * Nat.fib (2 * N - 3) +
        N * (N - 1) * (N - 2) * (N - 3) * Nat.fib (2 * N - 4)

/-- For `h(x) = ∑_{j=0}^t A_j x^j ∈ ℂ[x]`,
`∑_{k=1}^N h(k) binom(N, k) F_k = ∑_{j=0}^t A_j ∑_{i=0}^j {j, i} (N)_i F_{2N-i}`, and for
`t = 4` this equals `A_0 F_{2N} + (A_1 + A_2 + A_3 + A_4) binom(N,1) F_{2N-1}
+ 2(A_2 + 3A_3 + 7A_4) binom(N,2) F_{2N-2} + 6(A_3 + 6A_4) binom(N,3) F_{2N-3}
+ 24 A_4 binom(N,4) F_{2N-4}`. The paper's hypotheses `N, t > 0` and `t ≤ N/2` are not needed
and are dropped.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 2.7. -/
public theorem_wanted sum_poly_mul_choose_mul_fib (A : ℕ → ℂ) (N t : ℕ) :
    (∑ k ∈ Finset.Icc 1 N,
        (∑ j ∈ Finset.range (t + 1), A j * (k : ℂ) ^ j) * N.choose k * Nat.fib k =
      ∑ j ∈ Finset.range (t + 1), A j * ∑ i ∈ Finset.range (j + 1),
        (Nat.stirlingSecond j i : ℂ) * N.descFactorial i * Nat.fib (2 * N - i)) ∧
    ∑ k ∈ Finset.Icc 1 N,
        (∑ j ∈ Finset.range 5, A j * (k : ℂ) ^ j) * N.choose k * Nat.fib k =
      A 0 * Nat.fib (2 * N) + (A 1 + A 2 + A 3 + A 4) * N.choose 1 * Nat.fib (2 * N - 1) +
        2 * (A 2 + 3 * A 3 + 7 * A 4) * N.choose 2 * Nat.fib (2 * N - 2) +
        6 * (A 3 + 6 * A 4) * N.choose 3 * Nat.fib (2 * N - 3) +
        24 * A 4 * N.choose 4 * Nat.fib (2 * N - 4)

/-- For a real sequence `U_{n+1} = a U_n + b U_{n-1}` with `a² + 4b ≠ 0`, roots `α ≠ β` of
`y² = a y + b` (taken in `ℂ`, characterized by `α + β = a`, `α β = -b`),
`A = (U_1 - U_0 β)/(α - β)`, `B = (U_1 - U_0 α)/(α - β)`, and `h(x) = ∑_{j=0}^t c_j x^j ∈ ℂ[x]`:
`∑_{k=0}^N h(k) binom(N, k) U_k^r x^k = ∑_{j=0}^t c_j ∑_{i=0}^j {j, i} x^i
∑_{ℓ=0}^r binom(r, ℓ) A^ℓ (-B)^{r-ℓ} (N)_i (α^ℓ β^{r-ℓ})^i (1 + α^ℓ β^{r-ℓ} x)^{N-i}`.
The paper prints `A^j` (the outer index) where its proof, via the cited identity
`∑_k binom(N,k) U_k^r x^k = ∑_j binom(r,j) A^j (-B)^{r-j} (1 + α^j β^{r-j} x)^N`, gives `A^ℓ`; the
printed form fails for `F_k`, `h = 1`, `r = N = 1`, `x = 0` (left side `0`, printed right side
`1 - 1/√5`). The paper's `h` coefficients `A_j` are renamed `c j`; positivity of `r, N, t` is
dropped.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 2.8. -/
public theorem_wanted sum_poly_mul_choose_mul_secondOrder_pow (a b : ℝ) (U : ℕ → ℝ)
    (hU : ∀ n, U (n + 2) = a * U (n + 1) + b * U n) (α β : ℂ) (hαβ : α ≠ β)
    (hsum : α + β = a) (hprod : α * β = -b) (c : ℕ → ℂ) (t N r : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (N + 1),
        (∑ j ∈ Finset.range (t + 1), c j * (k : ℂ) ^ j) * N.choose k * (U k : ℂ) ^ r * x ^ k =
      ∑ j ∈ Finset.range (t + 1), c j * ∑ i ∈ Finset.range (j + 1),
        (Nat.stirlingSecond j i : ℂ) * x ^ i * ∑ l ∈ Finset.range (r + 1),
          (r.choose l : ℂ) * ((U 1 - U 0 * β) / (α - β)) ^ l *
            (-((U 1 - U 0 * α) / (α - β))) ^ (r - l) * N.descFactorial i *
            (α ^ l * β ^ (r - l)) ^ i * (1 + α ^ l * β ^ (r - l) * x) ^ (N - i)

/-- For `s ≥ 1`, `∑_{k=0}^N binom(N, k) x^{k+s} / (k+1)^{(s)} =
((1 + x)^{N+s} - 1)/(N+1)^{(s)} - ∑_{j=1}^{s-1} x^j / (j! (N+1)^{(s-j)})` (the paper writes
`binom(n, k)` for `binom(N, k)`).

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 3.1, equation (3.1). -/
public theorem_wanted sum_choose_mul_pow_div_ascFactorial (N s : ℕ) (hs : 0 < s) (x : ℝ) :
    ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * x ^ (k + s) / (k + 1).ascFactorial s =
      ((1 + x) ^ (N + s) - 1) / (N + 1).ascFactorial s -
        ∑ j ∈ Finset.Icc 1 (s - 1), x ^ j / (j.factorial * (N + 1).ascFactorial (s - j))

/-- For `f(x) = ∑_{k=0}^N a_k x^k` and iterated antiderivatives `I_0 = f`, `I_j' = I_{j-1}`
(with arbitrary constants), `∑_{k=0}^N a_k x^{k+s} / (k+1)^{(s)} =
I_s(x) - ∑_{j=1}^s I_j(0) x^{s-j}/(s-j)!`. The paper's `s > 0` is dropped (`s = 0` is
`f(x) = I_0(x)`).

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Theorem 3.1, equation (3.2). -/
public theorem_wanted sum_coeff_mul_pow_div_ascFactorial_eq_antideriv (a : ℕ → ℝ) (N s : ℕ)
    (I : ℕ → ℝ → ℝ) (hI0 : ∀ y, I 0 y = ∑ k ∈ Finset.range (N + 1), a k * y ^ k)
    (hI : ∀ j y, HasDerivAt (I (j + 1)) (I j y) y) (x : ℝ) :
    ∑ k ∈ Finset.range (N + 1), a k * x ^ (k + s) / (k + 1).ascFactorial s =
      I s x - ∑ j ∈ Finset.Icc 1 s, I j 0 * x ^ (s - j) / (s - j).factorial

/-- Epsteen's identity (3.4): `∑_{k=0}^n binom(n, k)/(k + 1) = (2^{n+1} - 1)/(n + 1)`.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 3.2. -/
public theorem_wanted sum_choose_div_succ (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) / (k + 1) = (2 ^ (n + 1) - 1) / (n + 1)

/-- Finkel's identity (3.5): `∑_{k=1}^n (-1)^{k-1} binom(n, k)/k = H_n`.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 3.2. -/
public theorem_wanted sum_neg_one_pow_choose_div_eq_harmonic (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (-1 : ℚ) ^ (k - 1) * n.choose k / k = harmonic n

/-- Identity (3.6): `∑_{k=1}^n binom(n, k) x^k / k² =
∑_{k=1}^n (1/k) ∑_{j=1}^k (1 + x)^j / j - ∑_{k=1}^n (1/k) ∑_{j=1}^k 1/j` for real `x`.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 3.2. -/
public theorem_wanted sum_choose_mul_pow_div_sq (n : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.Icc 1 n, (n.choose k : ℝ) * x ^ k / (k : ℝ) ^ 2 =
      ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) * ∑ j ∈ Finset.Icc 1 k, (1 + x) ^ j / j -
        ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) * ∑ j ∈ Finset.Icc 1 k, 1 / (j : ℝ)

/-- The case `x = -1` of (3.6): `∑_{k=1}^n (-1)^{k-1} binom(n, k)/k² = ∑_{k=1}^n H_k / k`.

Source: Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of
Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci
Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 3.2. -/
public theorem_wanted sum_neg_one_pow_choose_div_sq_eq_sum_harmonic (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (-1 : ℚ) ^ (k - 1) * n.choose k / (k : ℚ) ^ 2 =
      ∑ k ∈ Finset.Icc 1 n, harmonic k / k

end

end MetaMathlibExt
