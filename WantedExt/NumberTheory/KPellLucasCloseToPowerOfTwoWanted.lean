/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.NumberTheory.KPellLucasCloseToPowerOfTwo
public import MathlibExt.NumberTheory.KPellLucasDominantRoot

/-!
# `k`-Pell–Lucas numbers close to a power of 2

Statements from Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers
Close to a Power of 2*, INTEGERS 25 (2025), Article A67. The recurrence and Lemmas 6–8 are in
`MathlibExt.NumberTheory.KPellLucasCloseToPowerOfTwo`.

The `k`-generalized Pell–Lucas sequence starts with `k - 2` zeros followed by `Q_0 = Q_1 = 2`,
and `Q_n = 2 Q_{n-1} + Q_{n-2} + ⋯ + Q_{n-k}` for `n ≥ 2`; here it is `kPellLucas k n` for
`n ≥ 0`. Its characteristic polynomial is `Φ_k(x) = x^k - 2x^{k-1} - x^{k-2} - ⋯ - x - 1`, with
one positive real root `α`, and `g_k(z) = (z - 1) / ((k + 1) z² - 3kz + k - 1)`. An integer `a`
is close to `2^m` when `|a - 2^m| < 2^{m/2}`.
-/

namespace MetaMathlibExt

open Real

@[expose] public section

/-- **$k$-Pell–Lucas numbers that are powers of two (Corollary 1).** Let $k \ge 2$, $n \ge 1$ and
$m \ge 1$ be natural numbers, and let $Q^{(k)}_n$ be the $n$th $k$-Pell–Lucas number. Then
$Q^{(k)}_n = 2^m$ if and only if either $n = 1$ and $m = 1$, or $n = 3$, $m = 4$ and $k \ge 3$.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Corollary 1 (`integers-2025-A67-cor-1`). -/
public theorem_wanted kPellLucas_eq_two_pow_iff (k n m : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (hm : 1 ≤ m) :
    kPellLucas k n = 2 ^ m ↔ (n = 1 ∧ m = 1) ∨ (n = 3 ∧ m = 4 ∧ 3 ≤ k)

/-- **Bounds for the dominant root of the $k$-Pell–Lucas polynomial (Lemma 1).** Let $k \ge 2$ be
a natural number and let $\alpha > 0$ be a real number with
$\alpha^k = 2\alpha^{k-1} + \sum_{i=0}^{k-2} \alpha^i$, that is, a positive real root of
$\Phi_k(x) = x^k - 2x^{k-1} - \sum_{i=0}^{k-2} x^i$. Write
$g_k(z) = (z - 1) / ((k + 1) z^2 - 3kz + k - 1)$ and let $\varphi$ be the golden ratio. Then
(a) $0.276 < g_k(\alpha) < 0.5$, and $|g_k(\beta)| < 1$ for every complex root $\beta \ne \alpha$
of $\Phi_k$; and (b) $\varphi^2 (1 - \varphi^{-k}) < \alpha < \varphi^2$.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 1 (`integers-2025-A67-lem-1`). -/
public theorem_wanted kPellLucas_dominantRoot_bounds (k : ℕ) (hk : 2 ≤ k) (α : ℝ) (hα : 0 < α)
    (hroot : α ^ k = 2 * α ^ (k - 1) + ∑ i ∈ Finset.range (k - 1), α ^ i) :
    (0.276 < (α - 1) / ((k + 1) * α ^ 2 - 3 * k * α + k - 1) ∧
      (α - 1) / ((k + 1) * α ^ 2 - 3 * k * α + k - 1) < 0.5 ∧
      ∀ β : ℂ, β ^ k = 2 * β ^ (k - 1) + ∑ i ∈ Finset.range (k - 1), β ^ i → β ≠ α →
        ‖(β - 1) / ((k + 1) * β ^ 2 - 3 * k * β + k - 1)‖ < 1) ∧
    goldenRatio ^ 2 * (1 - (goldenRatio ^ k)⁻¹) < α ∧ α < goldenRatio ^ 2

/-- **Golden-ratio approximations at the dominant root (Lemma 2).** Let $\varphi$ be the golden
ratio, let $k$ and $n$ be natural numbers with $k \ge 50$ and $1 < n < \varphi^{k/2}$, and let
$\alpha > 0$ be a real number with $\alpha^k = 2\alpha^{k-1} + \sum_{i=0}^{k-2} \alpha^i$. Write
$g_k(z) = (z - 1) / ((k + 1) z^2 - 3kz + k - 1)$. Then
(i) $|(2\alpha - 2)\alpha^n - 2\varphi^{2n+1}| < 4\varphi^{2n} / \varphi^{k/2}$ and
(ii) $|g_k(\alpha) - g_k(\varphi^2)| < 4k / \varphi^k$.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 2 (`integers-2025-A67-lem-2`). -/
public theorem_wanted kPellLucas_dominantRoot_golden_approx (k n : ℕ) (hk : 50 ≤ k) (hn : 1 < n)
    (hnk : (n : ℝ) < goldenRatio ^ ((k : ℝ) / 2)) (α : ℝ) (hα : 0 < α)
    (hroot : α ^ k = 2 * α ^ (k - 1) + ∑ i ∈ Finset.range (k - 1), α ^ i) :
    |(2 * α - 2) * α ^ n - 2 * goldenRatio ^ (2 * n + 1)| <
        4 * goldenRatio ^ (2 * n) / goldenRatio ^ ((k : ℝ) / 2) ∧
      |(α - 1) / ((k + 1) * α ^ 2 - 3 * k * α + k - 1) -
          (goldenRatio ^ 2 - 1) /
            ((k + 1) * (goldenRatio ^ 2) ^ 2 - 3 * k * goldenRatio ^ 2 + k - 1)| <
        4 * k / goldenRatio ^ k

/-- **Continued-fraction lower bound for rational approximations.** Let $\tau$ be an irrational real
number with simple continued fraction expansion $[a_0; a_1, a_2, \ldots]$, so that
$a_0 = \lfloor \tau \rfloor$, and let $q_0, q_1, \ldots$ be the denominators of its convergents. Let
$M > 0$ be a real number, let $N$ be the least positive integer with $q_N > M$, and put
$a(M) = \max \{a_k : 0 \le k \le N\}$. Then

$$\left|\tau - \frac{y}{x}\right| > \frac{1}{(a(M) + 2)\, x^2}$$

for all integers $x$ and $y$ with $0 < x < M$.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 5 (`integers-2025-A67-lem-5`). -/
public theorem_wanted lt_abs_sub_div_of_max_partialQuotient (τ : ℝ) (hτ : Irrational τ) (M : ℝ)
    (hM : 0 < M) (N : ℕ) (hN : 0 < N) (hqN : M < (GenContFract.of τ).dens N)
    (hNmin : ∀ j, 0 < j → j < N → (GenContFract.of τ).dens j ≤ M) (a : ℕ → ℝ)
    (ha₀ : a 0 = (GenContFract.of τ).h)
    (ha : ∀ j, (GenContFract.of τ).partDens.get? j = some (a (j + 1))) (x y : ℤ) (hx : 0 < x)
    (hxM : (x : ℝ) < M) :
    1 / (((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one a + 2) * (x : ℝ) ^ 2) <
      |τ - y / x|

/-- **Absolute bounds for $k$-Pell–Lucas numbers close to a power of two (Lemma 9).** Let $k$, $n$
and $m$ be natural numbers with $k \ge 2$, $m \ge 1$ and $n \ge k + 1$, and let $Q^{(k)}_n$ be
the $n$th $k$-Pell–Lucas number. If $|Q^{(k)}_n - 2^m| < 2^{m/2}$, then
$n < 1.7 \cdot 10^{15} \, k^4 (\log k)^3$ and $m < 2.37 \cdot 10^{15} \, k^4 (\log k)^3$.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 9 (`integers-2025-A67-lem-9`). -/
public theorem_wanted kPellLucas_close_two_pow_lt_bounds (k n m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (hkn : k + 1 ≤ n) (hclose : |(kPellLucas k n : ℝ) - 2 ^ m| < (2 : ℝ) ^ ((m : ℝ) / 2)) :
    (n : ℝ) < 1.7e15 * k ^ 4 * Real.log k ^ 3 ∧ (m : ℝ) < 2.37e15 * k ^ 4 * Real.log k ^ 3

/-- **No $k$-Pell–Lucas number with $k > 350$ and index $n \ge k + 1$ is close to a power of
two (Lemma 10).** For all natural numbers $k$, $n$ and $m$ with $k > 350$ and $n \ge k + 1$, the
$n$th $k$-Pell–Lucas number $Q^{(k)}_n$ satisfies $|Q^{(k)}_n - 2^m| \ge 2^{m/2}$.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 10 (`integers-2025-A67-lem-10`). -/
public theorem_wanted kPellLucas_not_close_two_pow_of_large_order (k n m : ℕ) (hk : 350 < k)
    (hkn : k + 1 ≤ n) : ¬ |(kPellLucas k n : ℝ) - 2 ^ m| < (2 : ℝ) ^ ((m : ℝ) / 2)

end

end MetaMathlibExt
