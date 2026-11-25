/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.NumberTheory.Bernoulli
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.LinearCombination

/-!
# Derivatives of the Bernoulli–Fibonacci expansion of `(x + β)^m`

This file defines the constants `sqrt5`, `fibAlpha` and `fibBeta` (`√5`, the golden ratio
`α = (1 + √5)/2` and its conjugate `β = (1 - √5)/2`) used by the statements from Bensaci,
Boumahdi and Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers", *Journal of Integer
Sequences* 27 (2024), Article 24.7.2, and proves the derivative form of the Bernoulli–Fibonacci
expansion of `(x + β)^m` from that paper. The docstring of `descFactorial_mul_add_fibBeta_pow`
records the correction to the printed statement.

The three constants are the first declarations of the file, in the order of
`WantedExt.NumberTheory.FiniteSumsFibLucasWanted` where they were introduced, so that their
elaborated terms, including the names of the auxiliary proofs of `Nat.AtLeastTwo` that Lean
shares between them, are unchanged.

Binet's formula and the generating series of the Bernoulli numbers show that the inner
coefficient `∑ k ∈ range (n + 1), √5 ^ k * n.choose k * B k * F (n - k + 1) / (n - k + 1)` is
`β ^ n`. The identity then follows from the binomial theorem for `(β + x) ^ (m - s)` and the
identity `m.descFactorial s * (m - s).choose n = m.choose n * (m - n).descFactorial s`.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.FiniteSumsFibLucasWanted

/-- **The square root of five.** This is the real number $\sqrt{5}$, the nonnegative real square
root of $5$. -/
noncomputable def sqrt5 : ℝ := Real.sqrt 5

/-- **The golden ratio $\alpha$.** The golden ratio is the real number
$\alpha = (1 + \sqrt{5})/2$. -/
noncomputable def fibAlpha : ℝ := (1 + Real.sqrt 5) / 2

/-- **The conjugate golden ratio $\beta$.** The real number $\beta = (1 - \sqrt{5})/2$, the
conjugate of the golden ratio $(1 + \sqrt{5})/2$. -/
noncomputable def fibBeta : ℝ := (1 - Real.sqrt 5) / 2

open PowerSeries Finset
open scoped goldenRatio

-- The generating-series lemmas below repeat private lemmas of
-- `MathlibExt.NumberTheory.BernoulliFibonacciMultinomial`.

/-- The exponential generating series of `F_(j+1) / (j+1)`. -/
private noncomputable def fibSeries : PowerSeries ℝ :=
  mk fun j => (Nat.fib (j + 1) : ℝ) / (j + 1 : ℕ) / j.factorial

/-- The exponential generating series of `√5^k B_k`. -/
private noncomputable abbrev bernSeries :=
  rescale (Real.sqrt 5) (bernoulliPowerSeries ℝ)

/-- The exponential series of `a t`. -/
private noncomputable abbrev expSeries (a : ℝ) := rescale a (exp ℝ)

/-- Binet's formula: `√5 t` times the series of `F_(j+1) / (j+1)` is `e^(φ t) - e^(ψ t)`. -/
private theorem fibSeries_mul_scaled_X :
    fibSeries * (C (Real.sqrt 5) * X) = expSeries φ - expSeries ψ := by
  rw [← mul_assoc]
  ext n
  cases n with
  | zero =>
    simp only [coeff_zero_mul_X, map_sub, expSeries, coeff_rescale, pow_zero, one_mul, sub_self]
  | succ n =>
    rw [coeff_succ_mul_X, coeff_mul_C, fibSeries, coeff_mk, Real.coe_fib_eq]
    simp [expSeries, Nat.factorial_succ, field]

/-- The product of the Fibonacci and Bernoulli series is the exponential series at `ψ`. -/
private theorem fibSeries_mul_bernSeries : fibSeries * bernSeries = expSeries ψ := by
  have hB : bernSeries * (expSeries (Real.sqrt 5) - 1) = C (Real.sqrt 5) * X := by
    simpa [bernSeries, expSeries] using
      congrArg (rescale (Real.sqrt 5)) (bernoulliPowerSeries_mul_exp_sub_one ℝ)
  have hφ : expSeries (Real.sqrt 5) * expSeries ψ = expSeries φ := by
    rw [expSeries, expSeries, exp_mul_exp_eq_exp_add, ← Real.goldenRatio_sub_goldenConj,
      sub_add_cancel]
  have hne : C (Real.sqrt 5) * (X : PowerSeries ℝ) ≠ 0 :=
    mul_ne_zero (by simp [Real.sqrt_ne_zero'.mpr (by norm_num : 0 < (5 : ℝ))]) X_ne_zero
  apply mul_right_cancel₀ hne
  calc
    _ = (expSeries φ - expSeries ψ) * bernSeries := by rw [← fibSeries_mul_scaled_X]; ring
    _ = expSeries ψ * (bernSeries * (expSeries (Real.sqrt 5) - 1)) := by rw [← hφ]; ring
    _ = _ := by rw [hB]

/-- The inner Bernoulli–Fibonacci coefficient is a power of the conjugate golden ratio. -/
private theorem sum_bernoulli_fib_eq_fibBeta_pow (n : ℕ) :
    ∑ k ∈ range (n + 1),
        (Real.sqrt 5) ^ k * (Nat.choose n k : ℝ) * (bernoulli k : ℝ) *
          ((Nat.fib (n - k + 1) : ℝ) / (n - k + 1 : ℕ)) = fibBeta ^ n := by
  calc
    _ = (n.factorial : ℝ) * coeff n (bernSeries * fibSeries) := by
      rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
      refine sum_congr rfl fun k hk => ?_
      rw [Nat.cast_choose ℝ (mem_range_succ_iff.mp hk)]
      simp only [fibSeries, bernSeries, bernoulliPowerSeries, coeff_mk, coeff_rescale, map_div₀,
        map_natCast, eq_ratCast]
      field_simp
    _ = fibBeta ^ n := by
      rw [mul_comm bernSeries, fibSeries_mul_bernSeries]
      simp [expSeries, coeff_exp, fibBeta, field]

/-- Choosing an ordered `s`-tuple and then an `n`-subset of the rest, out of `m` elements, is the
same as choosing the `n`-subset first. -/
private theorem descFactorial_mul_choose_sub (m s n : ℕ) :
    m.descFactorial s * (m - s).choose n = m.choose n * (m - n).descFactorial s := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  have h1 := Nat.choose_mul (n := m) (k := n + s) (s := s) (Nat.le_add_left s n)
  have h2 := Nat.choose_mul (n := m) (k := n + s) (s := n) (Nat.le_add_right n s)
  rw [Nat.add_sub_cancel, ← Nat.choose_symm_add] at h1
  rw [Nat.add_sub_cancel_left] at h2
  calc s.factorial * m.choose s * (m - s).choose n
        = s.factorial * (m.choose s * (m - s).choose n) := by ring
    _ = s.factorial * (m.choose n * (m - n).choose s) := by rw [← h1, h2]
    _ = _ := by ring

/-- **Derivatives of the Bernoulli–Fibonacci expansion of $(x + \beta)^m$.** Let
$\beta = (1 - \sqrt{5})/2$, let $B_k$ be the Bernoulli numbers with $B_1 = -1/2$, let $F_k$ be the
Fibonacci numbers, and write $a^{\underline{s}} = a(a-1)\cdots(a-s+1)$ for the falling factorial.
Then for all natural numbers $s \le m$ and every real number $x$,
$$
m^{\underline{s}} (x + \beta)^{m-s} = \sum_{n=0}^{m} \sum_{k=0}^{n} \sqrt{5}^{\,k} \binom{n}{k}
\binom{m}{n} B_k \frac{F_{n-k+1}}{n-k+1} (m-n)^{\underline{s}} x^{m-n-s},
$$
where the terms with $m - n < s$ are $0$ because $(m-n)^{\underline{s}} = 0$ there.

This is the paper's Corollary 4, obtained by differentiating Theorem 1 $s$ times; the printed
falling factorial of $m - n + 1$ is off by one, and the identity is written here multiplied
through by $m^{\underline{s}}$.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 4. -/
theorem descFactorial_mul_add_fibBeta_pow (m s : ℕ)
    (hs : s ≤ m) (x : ℝ) :
    (Nat.descFactorial m s : ℝ) * (x + fibBeta) ^ (m - s) =
      ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (Real.sqrt 5) ^ k * (Nat.choose n k : ℝ) *
          (Nat.choose m n : ℝ) * (bernoulli k : ℝ) *
          ((Nat.fib (n - k + 1) : ℝ) / (n - k + 1 : ℕ)) *
          (Nat.descFactorial (m - n) s : ℝ) * x ^ (m - n - s) := by
  have hinner : ∀ n ∈ range (m + 1), (∑ k ∈ range (n + 1),
        (Real.sqrt 5) ^ k * (Nat.choose n k : ℝ) *
          (Nat.choose m n : ℝ) * (bernoulli k : ℝ) *
          ((Nat.fib (n - k + 1) : ℝ) / (n - k + 1 : ℕ)) *
          (Nat.descFactorial (m - n) s : ℝ) * x ^ (m - n - s)) =
        fibBeta ^ n * ((Nat.choose m n : ℝ) * (Nat.descFactorial (m - n) s : ℝ) *
          x ^ (m - n - s)) := by
    intro n _
    rw [← sum_bernoulli_fib_eq_fibBeta_pow n, sum_mul]
    exact sum_congr rfl fun k _ => by ring
  -- Only the terms with `n ≤ m - s` survive; they are the binomial expansion of `(β + x)^(m-s)`.
  rw [sum_congr rfl hinner,
    ← sum_subset (range_subset_range.mpr (by omega : m - s + 1 ≤ m + 1)) ?_]
  · rw [add_comm, add_pow, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    have key := congrArg (Nat.cast : ℕ → ℝ) (descFactorial_mul_choose_sub m s n)
    push_cast at key
    rw [show m - s - n = m - n - s by omega]
    linear_combination (fibBeta ^ n * x ^ (m - n - s)) * key
  · intro n hn hn'
    simp only [mem_range] at hn hn'
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : m - n < s)]

end MathlibExt.NumberTheory.FiniteSumsFibLucasWanted
