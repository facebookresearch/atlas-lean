/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.FineNumber
public import MathlibExt.Combinatorics.Enumerative.WhittGeneralizedCatalan
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Sabar's triangle `s(n, i)`: harmonic, Fine and generalized Catalan numbers

Statements from Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*,
INTEGERS 26 (2026), Article A27.

The triangle is `s(n, i) = ∑_{j=i+1}^{n} (-1)^{n-j} C(j, i)` for `0 ≤ i ≤ n - 1` (OEIS A341091),
`sabarNumber` below. The Fine numbers `f_n` (`1, 0, 1, 2, 6, 18, …`, OEIS A000957, indexed as in
the paper) are `MetaMathlibExt.fineNumber`, the Catalan numbers `C(n)` are Mathlib's `catalan`,
`H_n` is `harmonic`, and `C_n = (1/n) ∑_{i=0}^{n-1} C(n-1, i)⁻¹` is written out. The generalized
Catalan numbers `C(α, n)` of Whitt are `MetaMathlibExt.whittGeneralizedCatalan` (MathlibExt).

The paper's Theorem 1 (a closed form through `₂F₁(1, n+2; n+2-i; -1)`, a value outside the disc
of convergence of the hypergeometric series) is not stated; see the audit table.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Sabar's triangle.** For natural numbers $n$ and $i$, the entry $s(n, i)$ of Sabar's triangle
is the integer
$$s(n, i) = \sum_{j=i+1}^{n} (-1)^{n-j} \binom{j}{i}.$$
In particular $s(n, i) = 0$ for $i \ge n$, the empty sum.

In the source, $s(n, i)$ counts certain grid paths; for $0 \le i \le n - 1$ these numbers form
OEIS A341091.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Section 2 (definition of `s(n, i)`). -/
public def sabarNumber (n i : ℕ) : ℤ :=
  ∑ j ∈ Finset.Ioc i n, (-1) ^ (n - j) * (j.choose i : ℤ)

/-- **Rows 5 and 10 of Sabar's triangle.** The entries $s(5, i)$ of Sabar's triangle for
$i = 0, 1, \dots, 4$ are $1, 2, 7, 6, 5$, and the entries $s(10, i)$ for $i = 0, 1, \dots, 9$
are $0, 6, 24, 71, 129, 167, 147, 92, 36, 10$.

These are rows $n = 5$ and $n = 10$ of the source's Table 1.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Table 1. -/
public theorem sabarNumber_rows_five_ten :
    (List.range 5).map (sabarNumber 5) = [1, 2, 7, 6, 5] ∧
      (List.range 10).map (sabarNumber 10) = [0, 6, 24, 71, 129, 167, 147, 92, 36, 10] := by
  decide +kernel

/-- **A recurrence for Sabar's triangle in small cases.** For all natural numbers $n$ and $i$ with
$i < n < 8$, the entries of Sabar's triangle $s$ satisfy
$s(n + 2, i + 1) = s(n, i + 1) + \binom{n+1}{i}$.

This is the source's third basic identity $s(n, i) = s(n-2, i) + \binom{n-1}{i-1}$, stated here
only in these cases. It fails for $i = n$ and $i = n + 1$ (for $i \ge n + 2$ both sides are $0$):
for example $s(2, 1) = 2$ but $s(0, 1) + \binom{1}{0} = 1$.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Section 2 (identities following from the definition). -/
public theorem sabarNumber_recurrence_small :
    ∀ n < 8, ∀ i < n,
      sabarNumber (n + 2) (i + 1) = sabarNumber n (i + 1) + ((n + 1).choose i : ℤ) := by
  decide +kernel

/-- **Harmonic numbers from Sabar's triangle.** For every natural number $n \ge 2$, the harmonic
number $H_n = \sum_{k=1}^{n} \frac{1}{k}$ and the entries $s(n-1, i)$ of Sabar's triangle satisfy
$$H_n = \frac{1}{n} \sum_{i=0}^{n-1} \binom{n-1}{i}^{-1} +
\sum_{i=0}^{n-2} \frac{(-1)^{n-i} \, s(n-1, i)}{n-i}.$$

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Theorem 2 (`integers-2026-A27-thm-2`). -/
public theorem_wanted harmonic_eq_sum_inv_choose_add_sum_sabarNumber (n : ℕ) (hn : 2 ≤ n) :
    harmonic n =
      (1 / (n : ℚ)) * ∑ i ∈ Finset.range n, 1 / ((n - 1).choose i : ℚ) +
        ∑ i ∈ Finset.range (n - 1), (-1 : ℚ) ^ (n - i) * sabarNumber (n - 1) i / ((n - i : ℕ) : ℚ)

/-- **Reciprocal binomial sums from Sabar's triangle.** For every natural number $n \ge 2$, the
entries $s(n-1, i)$ of Sabar's triangle satisfy
$$\frac{1}{n+1} \sum_{i=0}^{n} \binom{n}{i}^{-1} =
1 + \sum_{i=0}^{n-2} \frac{(-1)^{n-i-1} \, s(n-1, i)}{(n-i)(n+1-i)}.$$

This is the source's Corollary 1 with the sign used in its proof. As printed, with $(-1)^{n-i}$,
it fails at $n = 2$: the left side is $5/6$ but $1 + s(1, 0)/(2 \cdot 3) = 7/6$.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Corollary 1 (`integers-2026-A27-cor-1`). -/
public theorem_wanted sum_inv_choose_succ_eq_one_add_sum_sabarNumber (n : ℕ) (hn : 2 ≤ n) :
    (1 / ((n + 1 : ℕ) : ℚ)) * ∑ i ∈ Finset.range (n + 1), 1 / (n.choose i : ℚ) =
      1 + ∑ i ∈ Finset.range (n - 1),
        (-1 : ℚ) ^ (n - i - 1) * sabarNumber (n - 1) i / (((n - i : ℕ) : ℚ) * ((n + 1 - i : ℕ) : ℚ))

/-- **The harmonic numbers as an alternating sum of Sabar numbers.** For every natural number
$n \ge 2$, writing $s(m, i)$ for Sabar's triangle and $H_n = \sum_{j=1}^{n} 1/j$ for the $n$-th
harmonic number, in the rational numbers

$$\sum_{i=0}^{2n-2} \frac{(-1)^i \, s(2n-1, i)}{i+1} = H_n.$$

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Theorem 3 (`integers-2026-A27-thm-3`). -/
public theorem_wanted sum_sabarNumber_div_succ_eq_harmonic (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ Finset.range (2 * n - 1), (-1 : ℚ) ^ i * sabarNumber (2 * n - 1) i / ((i + 1 : ℕ) : ℚ) =
      harmonic n

/-- **Fine numbers from Sabar's triangle.** For every natural number $n \ge 2$, the Fine number
$F(n)$ is the difference of two entries of row $2n$ of Sabar's triangle $s$:
$F(n) = s(2n, n+1) - s(2n, n-1)$.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Theorem 4 (`integers-2026-A27-thm-4`). -/
public theorem_wanted fineNumber_eq_sabarNumber_sub (n : ℕ) (hn : 2 ≤ n) :
    fineNumber n = (sabarNumber (2 * n) (n + 1) - sabarNumber (2 * n) (n - 1) : ℤ)

/-- **Sabar's alternating binomial sum equal to $n$.** For every natural number $n \ge 2$, in the
rational numbers,

$$\sum_{k=1}^{n} (-1)^{k+1} \left(1 - \frac{2k}{n+1} + \frac{n}{k+1}\right) \binom{n+k}{k} = n.$$

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Corollary 2 (`integers-2026-A27-cor-2`). -/
public theorem_wanted sum_neg_one_pow_mul_choose_eq_self (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, (-1 : ℚ) ^ (k + 1) *
        (1 - 2 * (k : ℚ) / (n + 1) + (n : ℚ) / (k + 1)) * ((n + k).choose k : ℚ) = n

/-- **Fine numbers as an alternating binomial sum.** For every natural number $n \ge 2$, the Fine
number $F(n)$ satisfies
$$F(n) = \frac{1}{2} (-1)^n +
\frac{1}{2} \sum_{k=0}^{n} (-1)^{n-k} \left(1 - \frac{n}{k+1}\right) \binom{n+k}{k}.$$

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Corollary 3 (`integers-2026-A27-cor-3`). -/
public theorem_wanted fineNumber_eq_half_neg_one_pow_add_sum (n : ℕ) (hn : 2 ≤ n) :
    fineNumber n = (1 / 2) * (-1 : ℚ) ^ n +
      (1 / 2) * ∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (n - k) * (1 - (n : ℚ) / (k + 1)) * ((n + k).choose k : ℚ)

/-- **Central entries of Sabar's triangle and Fine numbers.** Let $F(m)$ denote the Fine numbers
and $C_m$ the Catalan numbers. For every natural number $n \ge 1$, the entries of Sabar's
triangle $s$ satisfy
$$s(2n, n) = \frac{1}{6} \binom{2n+2}{n+1} + \frac{2}{3} F(n) + (-1)^{n+1},$$
$$s(2n, n) = \frac{1}{3} (2n+1) C_n + \frac{2}{3} F(n) + (-1)^{n+1},$$
$$s(2n, n) = \frac{2}{3} \binom{2n}{n} - \frac{1}{3} F(n-1) + (-1)^{n+1},$$
and
$$s(2n-1, n) = \frac{2}{3} \binom{2n-1}{n} + \frac{1}{3} F(n-1) + (-1)^n.$$

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Theorem 5 (`integers-2026-A27-thm-5`). -/
public theorem_wanted sabarNumber_central_eq_fineNumber (n : ℕ) (hn : 1 ≤ n) :
    (sabarNumber (2 * n) n : ℚ) =
        (1 / 6) * ((2 * n + 2).choose (n + 1) : ℚ) + (2 / 3) * fineNumber n + (-1) ^ (n + 1) ∧
      (sabarNumber (2 * n) n : ℚ) =
        (1 / 3) * (2 * n + 1) * (catalan n : ℚ) + (2 / 3) * fineNumber n + (-1) ^ (n + 1) ∧
      (sabarNumber (2 * n) n : ℚ) =
        (2 / 3) * ((2 * n).choose n : ℚ) - (1 / 3) * fineNumber (n - 1) + (-1) ^ (n + 1) ∧
      (sabarNumber (2 * n - 1) n : ℚ) =
        (2 / 3) * ((2 * n - 1).choose n : ℚ) + (1 / 3) * fineNumber (n - 1) + (-1) ^ n

/-- **Consecutive binomial sums weighted by powers of 2.** For a natural number $m$, let
$V_m(2) = \sum_{k=0}^{m} \binom{m+k}{k} 2^k$. For every natural number $n \ge 1$,
$V_n(2) + V_{n+1}(2) = 3 \cdot 2^n \binom{2n+2}{n+1}$.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Lemma 1 (`integers-2026-A27-lem-1`). -/
public theorem_wanted sum_choose_mul_two_pow_add_succ (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (n + k).choose k * 2 ^ k +
        ∑ k ∈ Finset.range (n + 2), (n + 1 + k).choose k * 2 ^ k =
      3 * 2 ^ n * (2 * n + 2).choose (n + 1)

/-- **Consecutive Whitt generalized Catalan numbers at $\alpha = 2$.** For every natural number
$n \ge 1$, Whitt's generalized Catalan numbers at $\alpha = 2$ satisfy

$$C(2, n) + C(2, n+1) = 2^{n+1} c_n,$$

where $c_n = \frac{1}{n+1}\binom{2n}{n}$ is the $n$-th Catalan number.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Theorem 6 (`integers-2026-A27-thm-6`). -/
public theorem_wanted whittGeneralizedCatalan_two_add_succ (n : ℕ) (hn : 1 ≤ n) :
    whittGeneralizedCatalan 2 n + whittGeneralizedCatalan 2 (n + 1) = 2 ^ (n + 1) * catalan n

/-- **Central entries of Sabar's triangle and Whitt's numbers.** Let $C(2, m)$ denote Whitt's
generalized Catalan numbers at $\alpha = 2$. For every natural number $n \ge 1$, the central
entry $s(2n, n)$ of Sabar's triangle satisfies
$$s(2n, n) = \frac{2}{3} \binom{2n}{n} - \frac{1}{3} \cdot \frac{C(2, n)}{2^{n+1}} +
(-1)^{n+1} + \frac{(-1)^n}{2^{n+1}}.$$

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Theorem 7 (`integers-2026-A27-thm-7`). -/
public theorem_wanted sabarNumber_central_eq_whittGeneralizedCatalan (n : ℕ) (hn : 1 ≤ n) :
    (sabarNumber (2 * n) n : ℚ) =
      (2 / 3) * ((2 * n).choose n : ℚ) - (1 / 3) * whittGeneralizedCatalan 2 n / 2 ^ (n + 1) +
        (-1) ^ (n + 1) + (-1) ^ n / 2 ^ (n + 1)

/-- **Fine numbers from Whitt's generalized Catalan numbers.** For every natural number $n \ge 1$,
the Fine number $F(n)$, indexed so that $F(0) = 1$ and $F(1) = 0$, and Whitt's generalized Catalan
number $C(2, n+1)$ at $\alpha = 2$ satisfy

$$2^{n+2} F(n) = C(2, n+1) + 3(-1)^n.$$

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Corollary 4 (`integers-2026-A27-cor-4`). -/
public theorem_wanted two_pow_mul_fineNumber_eq_whittGeneralizedCatalan (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (n + 2) * fineNumber n = whittGeneralizedCatalan 2 (n + 1) + 3 * (-1) ^ n

end

end MetaMathlibExt
