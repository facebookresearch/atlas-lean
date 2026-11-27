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
public import MathlibExt.NumberTheory.FibonacciBinomialSum
public import MathlibExt.NumberTheory.KFibonacciAlternatingBinomial
public import MathlibExt.NumberTheory.KFibonacciBinomialTruncation
public import MathlibExt.NumberTheory.KFibonacciTruncatedRecurrence

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

/-- **Lagrange inversion formula.** Let $f, g : \mathbb{C} \to \mathbb{C}$ be analytic at $z_0$.
There are $\varepsilon > 0$ and $\delta > 0$ such that for every $\alpha \in \mathbb{C}$ with
$|\alpha| < \delta$ the equation $w = z_0 + \alpha f(w)$ has exactly one solution $w$ with
$|w - z_0| < \varepsilon$, and for this solution the series
$\sum_{n \ge 1} \frac{\alpha^n}{n!} \frac{d^{n-1}}{dz^{n-1}} \bigl(f(z)^n g'(z)\bigr)\big|_{z=z_0}$
converges absolutely to $g(w) - g(z_0)$.

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

/-- **Binomial series for the powers of the dominant $k$-Fibonacci root.** Let $k \ge 2$ and let
$\rho_k > 0$ be a real number with $\rho_k^k = 1 + \rho_k + \dots + \rho_k^{k-1}$. For integers $a$
and $j \ge 0$ write $\binom{a}{j} = a(a-1)\cdots(a-j+1)/j!$. Then for every $n \ge 1$ the series
$S = \sum_{\ell \ge 0} \frac{1}{\ell+1} \binom{k(\ell+1)+\ell-n}{\ell} 2^{-(k+1)\ell}$ converges
absolutely and $\rho_k^n = 2^n - n\, 2^{n-k-1} S$.

For $n = 1$ this is the paper's series for $\rho_k$ itself.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, Theorem 3
(`jis-2024-24.1.1-thm-3`). -/
public theorem_wanted kFibonacci_root_pow_eq_binomial_series (k n : ℕ) (hk : 2 ≤ k)
    (hn : 1 ≤ n) (α : ℝ) (hα : 0 < α) (hroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i) :
    ∃ S : ℝ, HasSum (fun ℓ : ℕ => 1 / ((ℓ : ℝ) + 1) *
        ((Ring.choose ((k * (ℓ + 1) + ℓ : ℕ) - (n : ℤ)) ℓ : ℤ) : ℝ) / 2 ^ ((k + 1) * ℓ)) S ∧
      α ^ n = 2 ^ n - n * (2 : ℝ) ^ ((n : ℤ) - k - 1) * S

/-- **Binomial series for the powers of the golden ratio.** Let $\varphi = (1 + \sqrt{5})/2$ be
the golden ratio, and for an integer $x$ and a natural number $j$ let
$\binom{x}{j} = x(x-1)\cdots(x-j+1)/j!$. For every natural number $n \ge 1$ the series
$S_n = \sum_{\ell \ge 0} \frac{1}{\ell + 1} \binom{3\ell + 2 - n}{\ell} 2^{-3\ell}$ converges
absolutely and $\varphi^n = 2^n - n \, 2^{n-3} S_n$. Moreover, the series
$\sum_{\ell \ge 0} \frac{1}{\ell + 1} \binom{3\ell + 1}{\ell} 2^{-(3\ell + 2)}$ converges
absolutely to $2 - \varphi$.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, Corollary 5
(`jis-2024-24.1.1-cor-5`). -/
public theorem_wanted goldenRatio_pow_eq_binomial_series :
    (∀ n : ℕ, 1 ≤ n → ∃ S : ℝ, HasSum (fun ℓ : ℕ => 1 / ((ℓ : ℝ) + 1) *
        ((Ring.choose ((3 * ℓ + 2 : ℕ) - (n : ℤ)) ℓ : ℤ) : ℝ) / 2 ^ (3 * ℓ)) S ∧
      Real.goldenRatio ^ n = 2 ^ n - n * (2 : ℝ) ^ ((n : ℤ) - 3) * S) ∧
    HasSum (fun ℓ : ℕ => 1 / ((ℓ : ℝ) + 1) * ((3 * ℓ + 1).choose ℓ : ℝ) / 2 ^ (3 * ℓ + 2))
      (2 - Real.goldenRatio)

/-- **Binomial series summed at the $k$-Fibonacci root.** Let $k \ge 2$ be a natural number and
$\rho > 0$ a real number with $\rho^k = 1 + \rho + \cdots + \rho^{k-1}$, and for an integer $x$
and a natural number $j$ let $\binom{x}{j} = x(x-1)\cdots(x-j+1)/j!$. Then for every integer
$a$ the series below converges absolutely and
$$
\sum_{\ell \ge 0} \binom{(k+1)\ell + a}{\ell} 2^{-(k+1)\ell} =
\frac{2^{a+1} \rho^{-a}}{(k+1)\rho - 2k}.
$$

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, Theorem 6
(`jis-2024-24.1.1-thm-6`). -/
public theorem_wanted hasSum_choose_div_two_pow_kFibonacci_root (k : ℕ) (hk : 2 ≤ k) (a : ℤ)
    (α : ℝ) (hα : 0 < α) (hroot : α ^ k = ∑ i ∈ Finset.range k, α ^ i) :
    HasSum (fun ℓ : ℕ => ((Ring.choose (((k + 1) * ℓ : ℕ) + a) ℓ : ℤ) : ℝ) /
        2 ^ ((k + 1) * ℓ))
      ((2 : ℝ) ^ (a + 1) * α ^ (-a) / ((k + 1) * α - 2 * k))

/-- **Difference binomial series at the $k$-Fibonacci root.** Let $k \ge 2$ be a natural number
and $\rho > 0$ a real number with $\rho^k = 1 + \rho + \cdots + \rho^{k-1}$, and for an integer
$x$ and a natural number $j$ let $\binom{x}{j} = x(x-1)\cdots(x-j+1)/j!$. For every natural number
$n \ne 1$ the series below converges absolutely and
$$
2^{n-2} \sum_{\ell \ge 0} \left(\binom{(k+1)\ell - n}{\ell} - \binom{(k+1)\ell - n}{\ell - 1}\right)
2^{-(k+1)\ell} = \frac{\rho - 1}{(k+1)\rho - 2k} \rho^{n-1},
$$
where the term $\binom{(k+1)\ell - n}{\ell - 1}$ is taken to be $0$ for $\ell = 0$.

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

/-- **$k$-Fibonacci numbers as truncated binomial sums.** Let $k \ge 2$ and let
$(F_n)_{n \ge 0}$ be the $k$-Fibonacci sequence, given by $F_0 = \dots = F_{k-2} = 0$,
$F_{k-1} = 1$ and $F_{m+k} = F_m + F_{m+1} + \dots + F_{m+k-1}$ for all $m \ge 0$. For integers
$a$ and $j \ge 0$ write $\binom{a}{j} = a(a-1)\cdots(a-j+1)/j!$, and put $\binom{a}{-1} = 0$.
For $n \ge 2$ let $G_n^{(k)}$ be the truncated binomial sum
$G_n^{(k)} = 2^{n-2} \sum_{\ell=0}^{\lfloor (n-1)/(k+1) \rfloor} \left(\binom{(k+1)\ell-n}{\ell} -
\binom{(k+1)\ell-n}{\ell-1}\right) 2^{-(k+1)\ell}$. Then $F_{n+k-2} = G_n^{(k)}$ for every
$n \ge 2$.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1, Theorem 9
(`jis-2024-24.1.1-thm-9`). -/
public theorem_wanted kFibonacci_eq_kFibonacciBinomialTruncation (k n : ℕ) (hk : 2 ≤ k)
    (hn : 2 ≤ n) (F : ℕ → ℤ) (hF0 : ∀ i < k - 1, F i = 0) (hF1 : F (k - 1) = 1)
    (hrec : ∀ m, F (m + k) = ∑ i ∈ Finset.range k, F (m + i)) :
    (F (n + k - 2) : ℚ) = kFibonacciBinomialTruncation k n

/-- **Binomial-sum formula for the $k$-Fibonacci numbers.** Let $k \ge 2$ and let
$(F_n)_{n \ge 0}$ be the $k$-Fibonacci sequence, given by $F_0 = \dots = F_{k-2} = 0$,
$F_{k-1} = 1$ and $F_{m+k} = F_m + F_{m+1} + \dots + F_{m+k-1}$ for all $m \ge 0$. For integers
$a$ and $j \ge 0$ write $\binom{a}{j} = a(a-1)\cdots(a-j+1)/j!$, and put $\binom{a}{-1} = 0$.
Then for every $n \ge k$,
$$F_n = 2^{n-k} \sum_{\ell=0}^{\lfloor (n-k+1)/(k+1) \rfloor} \left(\binom{(k+1)\ell+k-n-2}{\ell} -
\binom{(k+1)\ell+k-n-2}{\ell-1}\right) 2^{-(k+1)\ell}.$$

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

end

end MetaMathlibExt
