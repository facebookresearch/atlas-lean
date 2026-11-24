/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.SabarFineNumberWhitt
public import MathlibExt.Combinatorics.Enumerative.SabarFineNumber
public import MathlibExt.Combinatorics.Enumerative.WhittGeneralizedCatalan
public import MathlibExt.Combinatorics.Enumerative.SabarTriangle
public import MathlibExt.Combinatorics.Enumerative.SabarWeightedBinomialSum
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Sabar's triangle `s(n, i)`: harmonic, Fine and generalized Catalan numbers

Statements from Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*,
INTEGERS 26 (2026), Article A27.

The triangle is `s(n, i) = ∑_{j=i+1}^{n} (-1)^{n-j} C(j, i)` for `0 ≤ i ≤ n - 1` (OEIS A341091),
`MetaMathlibExt.sabarNumber` (MathlibExt). The Fine numbers `f_n` (`1, 0, 1, 2, 6, 18, …`,
OEIS A000957, indexed as in the paper) are `MetaMathlibExt.fineNumber`, the Catalan numbers `C(n)`
are Mathlib's `catalan`, `H_n` is `harmonic`, and `C_n = (1/n) ∑_{i=0}^{n-1} C(n-1, i)⁻¹` is
written out. The generalized Catalan numbers `C(α, n)` of Whitt are
`MetaMathlibExt.whittGeneralizedCatalan` (MathlibExt).

The paper's Theorem 1 (a closed form through `₂F₁(1, n+2; n+2-i; -1)`, a value outside the disc
of convergence of the hypergeometric series) is not stated; see the audit table.

Proved in `MathlibExt.Combinatorics.Enumerative.SabarTriangle`, which this module imports: the
definition `sabarNumber` with its checks `sabarNumber_rows_five_ten` and
`sabarNumber_recurrence_small`, the reciprocal binomial sum identity
`sum_inv_choose_succ_eq_one_add_sum_sabarNumber`, and the alternating sum for harmonic numbers
`sum_sabarNumber_div_succ_eq_harmonic`.

The weighted binomial sum identity `sum_choose_mul_two_pow_add_succ` is proved in
`MathlibExt.Combinatorics.Enumerative.SabarWeightedBinomialSum`, also imported here.
-/

namespace MetaMathlibExt

@[expose] public section

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

end

end MetaMathlibExt
