/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.NormNum

/-!
# Lagrange inversion and the `k`-Fibonacci numbers

Statements from Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1
(arXiv `2307.14763`).

For `k ≥ 2` the `k`-Fibonacci sequence `F` has `F 0 = ⋯ = F (k - 2) = 0`, `F (k - 1) = 1`
and `F (n + k) = F n + ⋯ + F (n + k - 1)`; it is characterized here by these hypotheses.
The dominant root `ρ_k` of `x ^ k = x ^ (k - 1) + ⋯ + 1` is the unique positive real root
of that equation; it is characterized here by `0 < α` and `α ^ k = ∑ i < k, α ^ i`.

The paper's binomial coefficient `binom(a, b)` (`a, b ∈ ℤ`) is the falling-factorial
quotient for `b ≥ 0`, which is `Ring.choose` over `ℤ`. Negative lower indices only occur as
`binom(a, -1)` in the first term of a sum; in every statement below that term is `0` under
the stated hypotheses, and it is written as `0` (an `if` on the summation index).
-/

namespace MetaMathlibExt

@[expose] public section

/-- The truncated binomial sum `G_n^{(k)} = 2 ^ (n - 2) ∑_{0 ≤ ℓ ≤ (n - 1)/(k + 1)}
(binom((k + 1) ℓ - n, ℓ) - binom((k + 1) ℓ - n, ℓ - 1)) 2 ^ (-(k + 1) ℓ)`, defined in the
paper for `n, k ≥ 2`. The `ℓ = 0` term `binom(-n, -1)` vanishes for `n ≥ 2` and is written
as `0`.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, definition
before Proposition 10. -/
public def kFibonacciBinomialTruncation (k n : ℕ) : ℚ :=
  2 ^ ((n : ℤ) - 2) * ∑ ℓ ∈ Finset.range ((n - 1) / (k + 1) + 1),
    ((Ring.choose (((k + 1) * ℓ : ℕ) - (n : ℤ)) ℓ -
      (if ℓ = 0 then 0 else Ring.choose (((k + 1) * ℓ : ℕ) - (n : ℤ)) (ℓ - 1)) : ℤ) : ℚ) /
      2 ^ ((k + 1) * ℓ)

/-- `G_2^{(2)} = 1 = F_2`.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, definition
before Proposition 10. -/
public theorem kFibonacciBinomialTruncation_two_two : kFibonacciBinomialTruncation 2 2 = 1 := by
  norm_num [kFibonacciBinomialTruncation]

/-- `G_4^{(2)} = 3 = F_4`: the first value whose sum has two terms.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, definition
before Proposition 10. -/
public theorem kFibonacciBinomialTruncation_two_four : kFibonacciBinomialTruncation 2 4 = 3 := by
  norm_num [kFibonacciBinomialTruncation, Finset.sum_range_succ, Ring.choose_one_right]

/-- **Theorem 1 (Lagrange inversion formula).** Let `f` and `g` be analytic at `z₀`. For
`α` small, the equation `w = z₀ + α f(w)` has a unique solution `w` near `z₀`, and
`g(w) = g(z₀) + ∑_{n ≥ 1} αⁿ / n! (d/dz)^{n - 1}(fⁿ g')(z₀)`.

The paper's implicitly defined analytic `w` is made explicit as the unique solution in a
small ball; the sum is reindexed from `n - 1`. The second display (`g = id`) is the
special case and is not stated separately.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, Theorem 1
(`jis-2024-24.1.1-thm-1`). -/
public theorem_wanted lagrange_inversion_formula_analytic (z₀ : ℂ) (f g : ℂ → ℂ)
    (hf : AnalyticAt ℂ f z₀) (hg : AnalyticAt ℂ g z₀) :
    ∃ ε > 0, ∃ δ > 0, ∀ α : ℂ, ‖α‖ < δ →
      (∃! w, w ∈ Metric.ball z₀ ε ∧ w = z₀ + α * f w) ∧
      ∀ w ∈ Metric.ball z₀ ε, w = z₀ + α * f w →
        HasSum (fun m : ℕ => α ^ (m + 1) / ((m + 1).factorial : ℂ) *
            iteratedDeriv m (fun z => f z ^ (m + 1) * deriv g z) z₀)
          (g w - g z₀)

/-- **Theorem 3.** For `k ≥ 2` and `n ≥ 1`,
`ρ_kⁿ = 2ⁿ - n 2^{n - k - 1} ∑_{ℓ ≥ 0} 1/(ℓ + 1) binom(k(ℓ + 1) + ℓ - n, ℓ) 2^{-(k + 1)ℓ}`.

The series is asserted to converge. The particular case `n = 1` (the formula for `ρ_k`) is
the instance `n = 1` and is not stated separately.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, Theorem 3
(`jis-2024-24.1.1-thm-3`). -/
public theorem_wanted kFibonacci_root_pow_eq_binomial_series (k n : ℕ) (hk : 2 ≤ k)
    (hn : 1 ≤ n) (α : ℝ) (hα : 0 < α) (hroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i) :
    ∃ S : ℝ, HasSum (fun ℓ : ℕ => 1 / ((ℓ : ℝ) + 1) *
        ((Ring.choose ((k * (ℓ + 1) + ℓ : ℕ) - (n : ℤ)) ℓ : ℤ) : ℝ) / 2 ^ ((k + 1) * ℓ)) S ∧
      α ^ n = 2 ^ n - n * (2 : ℝ) ^ ((n : ℤ) - k - 1) * S

/-- **Corollary 5.** For `n ≥ 1`, with `φ` the golden ratio,
`φⁿ = 2ⁿ - n 2^{n - 3} ∑_{ℓ ≥ 0} 1/(ℓ + 1) binom(3ℓ + 2 - n, ℓ) 2^{-3ℓ}`; in particular
`φ = 2 - ∑_{ℓ ≥ 0} 1/(ℓ + 1) binom(3ℓ + 1, ℓ) 2^{-(3ℓ + 2)}`.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, Corollary 5
(`jis-2024-24.1.1-cor-5`). -/
public theorem_wanted goldenRatio_pow_eq_binomial_series :
    (∀ n : ℕ, 1 ≤ n → ∃ S : ℝ, HasSum (fun ℓ : ℕ => 1 / ((ℓ : ℝ) + 1) *
        ((Ring.choose ((3 * ℓ + 2 : ℕ) - (n : ℤ)) ℓ : ℤ) : ℝ) / 2 ^ (3 * ℓ)) S ∧
      Real.goldenRatio ^ n = 2 ^ n - n * (2 : ℝ) ^ ((n : ℤ) - 3) * S) ∧
    HasSum (fun ℓ : ℕ => 1 / ((ℓ : ℝ) + 1) * ((3 * ℓ + 1).choose ℓ : ℝ) / 2 ^ (3 * ℓ + 2))
      (2 - Real.goldenRatio)

/-- **Theorem 6.** For `k ≥ 2` and every integer `a`,
`∑_{ℓ ≥ 0} binom((k + 1)ℓ + a, ℓ) 2^{-(k + 1)ℓ} = 2^{a + 1} ρ_k^{-a} / ((k + 1)ρ_k - 2k)`.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, Theorem 6
(`jis-2024-24.1.1-thm-6`). -/
public theorem_wanted hasSum_choose_div_two_pow_kFibonacci_root (k : ℕ) (hk : 2 ≤ k) (a : ℤ)
    (α : ℝ) (hα : 0 < α) (hroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i) :
    HasSum (fun ℓ : ℕ => ((Ring.choose (((k + 1) * ℓ : ℕ) + a) ℓ : ℤ) : ℝ) /
        2 ^ ((k + 1) * ℓ))
      ((2 : ℝ) ^ (a + 1) * α ^ (-a) / ((k + 1) * α - 2 * k))

/-- **Theorem 8.** For `k ≥ 2` and `n ≥ 0` with `n ≠ 1`, the asymptotic equivalent
`As_n^{(k)} = (ρ_k - 1) / ((k + 1)ρ_k - 2k) ρ_k^{n - 1}` of `F_n^{(k)}` equals
`2^{n - 2} ∑_{ℓ ≥ 0} (binom((k + 1)ℓ - n, ℓ) - binom((k + 1)ℓ - n, ℓ - 1)) 2^{-(k + 1)ℓ}`.

The `ℓ = 0` term `binom(-n, -1)` is `0` for `n ≠ 1` and is written as `0`.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, Theorem 8
(`jis-2024-24.1.1-thm-8`), with `As_n^{(k)}` from equation (8). -/
public theorem_wanted hasSum_binomial_series_kFibonacci_asymptotic (k n : ℕ) (hk : 2 ≤ k)
    (hn : n ≠ 1) (α : ℝ) (hα : 0 < α) (hroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i) :
    HasSum (fun ℓ : ℕ => (2 : ℝ) ^ ((n : ℤ) - 2) *
        ((Ring.choose (((k + 1) * ℓ : ℕ) - (n : ℤ)) ℓ -
          (if ℓ = 0 then 0 else Ring.choose (((k + 1) * ℓ : ℕ) - (n : ℤ)) (ℓ - 1)) : ℤ) : ℝ) /
        2 ^ ((k + 1) * ℓ))
      ((α - 1) / ((k + 1) * α - 2 * k) * α ^ ((n : ℤ) - 1))

/-- **Theorem 9.** For `n, k ≥ 2`, `F_{n + k - 2}^{(k)} = G_n^{(k)}`, the truncated binomial
sum `kFibonacciBinomialTruncation k n`.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, Theorem 9
(`jis-2024-24.1.1-thm-9`). -/
public theorem_wanted kFibonacci_eq_kFibonacciBinomialTruncation (k n : ℕ) (hk : 2 ≤ k)
    (hn : 2 ≤ n) (F : ℕ → ℤ) (hF0 : ∀ i < k - 1, F i = 0) (hF1 : F (k - 1) = 1)
    (hrec : ∀ m, F (m + k) = ∑ i ∈ Finset.range k, F (m + i)) :
    (F (n + k - 2) : ℚ) = kFibonacciBinomialTruncation k n

/-- **Proposition 10.** For `k ≥ 2`, `G_n^{(k)} = 2^{n - 2}` for `2 ≤ n ≤ k + 1`, and
`G_{k + 2}^{(k)} = 2^k - 1`.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1,
Proposition 10 (`jis-2024-24.1.1-prop-10`). -/
public theorem_wanted kFibonacciBinomialTruncation_initial_values (k : ℕ) (hk : 2 ≤ k) :
    (∀ n, 2 ≤ n → n ≤ k + 1 → kFibonacciBinomialTruncation k n = 2 ^ (n - 2)) ∧
      kFibonacciBinomialTruncation k (k + 2) = 2 ^ k - 1

/-- **Proposition 11.** For `n, k ≥ 2`, `G_{n + k + 1}^{(k)} = 2 G_{n + k}^{(k)} - G_n^{(k)}`.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1,
Proposition 11 (`jis-2024-24.1.1-prop-11`). -/
public theorem_wanted kFibonacciBinomialTruncation_recurrence (k n : ℕ) (hk : 2 ≤ k)
    (hn : 2 ≤ n) :
    kFibonacciBinomialTruncation k (n + k + 1) =
      2 * kFibonacciBinomialTruncation k (n + k) - kFibonacciBinomialTruncation k n

/-- **Corollary 12.** For `n ≥ k ≥ 2`,
`F_n^{(k)} = 2^{n - k} ∑_{0 ≤ ℓ ≤ (n - k + 1)/(k + 1)} (binom((k + 1)ℓ - n + k - 2, ℓ) -
binom((k + 1)ℓ - n + k - 2, ℓ - 1)) 2^{-(k + 1)ℓ}`.

The `ℓ = 0` term `binom(k - n - 2, -1)` is `0` and is written as `0`.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1,
Corollary 12 (`jis-2024-24.1.1-cor-12`). -/
public theorem_wanted kFibonacci_eq_binomial_sum (k n : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (F : ℕ → ℤ) (hF0 : ∀ i < k - 1, F i = 0) (hF1 : F (k - 1) = 1)
    (hrec : ∀ m, F (m + k) = ∑ i ∈ Finset.range k, F (m + i)) :
    (F n : ℚ) = 2 ^ (n - k) * ∑ ℓ ∈ Finset.range ((n - k + 1) / (k + 1) + 1),
      ((Ring.choose (((k + 1) * ℓ + k : ℕ) - (n : ℤ) - 2) ℓ -
        (if ℓ = 0 then 0 else Ring.choose (((k + 1) * ℓ + k : ℕ) - (n : ℤ) - 2) (ℓ - 1)) :
          ℤ) : ℚ) / 2 ^ ((k + 1) * ℓ)

/-- **Corollary 13.** For `n ≥ 2`,
`F_n = 2^{n - 2} ∑_{0 ≤ ℓ ≤ (n - 1)/3} (binom(3ℓ - n, ℓ) - binom(3ℓ - n, ℓ - 1)) 2^{-3ℓ}`.

The `ℓ = 0` term `binom(-n, -1)` is `0` and is written as `0`.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1,
Corollary 13 (`jis-2024-24.1.1-cor-13`). -/
public theorem_wanted fib_eq_binomial_sum (n : ℕ) (hn : 2 ≤ n) :
    (Nat.fib n : ℚ) = 2 ^ (n - 2) * ∑ ℓ ∈ Finset.range ((n - 1) / 3 + 1),
      ((Ring.choose ((3 * ℓ : ℕ) - (n : ℤ)) ℓ -
        (if ℓ = 0 then 0 else Ring.choose ((3 * ℓ : ℕ) - (n : ℤ)) (ℓ - 1)) : ℤ) : ℚ) /
        2 ^ (3 * ℓ)

/-- **Corollary 14.** For `n ≥ k ≥ 2`,
`F_n^{(k)} = 2^{n - k} + ∑_{1 ≤ ℓ ≤ (n - k + 1)/(k + 1)} (-1)^ℓ (binom(n - (ℓ + 1)k + 2, ℓ) -
binom(n - (ℓ + 1)k, ℓ - 2)) 2^{n - (k + 1)ℓ - k}`.

The `ℓ = 1` term `binom(n - 2k, -1)` is `0` for `n ≠ 2k - 1` and is written as `0`. The
paper's hypothesis `n ≠ 2k - 1` is dropped: for `n = 2k - 1` the sum is empty and both
sides equal `2^{k - 1}`.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1,
Corollary 14 (`jis-2024-24.1.1-cor-14`). -/
public theorem_wanted kFibonacci_eq_alternating_binomial_sum (k n : ℕ) (hk : 2 ≤ k)
    (hkn : k ≤ n) (F : ℕ → ℤ) (hF0 : ∀ i < k - 1, F i = 0) (hF1 : F (k - 1) = 1)
    (hrec : ∀ m, F (m + k) = ∑ i ∈ Finset.range k, F (m + i)) :
    (F n : ℚ) = 2 ^ (n - k) + ∑ ℓ ∈ Finset.Icc 1 ((n - k + 1) / (k + 1)),
      (-1) ^ ℓ * ((Ring.choose ((n : ℤ) - (ℓ + 1) * k + 2) ℓ -
        (if ℓ = 1 then 0 else Ring.choose ((n : ℤ) - (ℓ + 1) * k) (ℓ - 2)) : ℤ) : ℚ) *
        (2 : ℚ) ^ ((n : ℤ) - (k + 1) * ℓ - k)

end

end MetaMathlibExt
