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
public import MathlibExt.Combinatorics.Enumerative.SabarFineNumberDifference
public import MathlibExt.Combinatorics.Enumerative.WhittGeneralizedCatalan
public import MathlibExt.Combinatorics.Enumerative.SabarTriangle
public import MathlibExt.Combinatorics.Enumerative.SabarHarmonicReciprocal
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

The Fine-number identity `fineNumber_eq_sabarNumber_sub` is proved in
`MathlibExt.Combinatorics.Enumerative.SabarFineNumberDifference`, also imported here.
-/

namespace MetaMathlibExt

@[expose] public section

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

end

end MetaMathlibExt
