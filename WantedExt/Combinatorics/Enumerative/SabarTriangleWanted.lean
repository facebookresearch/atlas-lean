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

This module only re-exports proved results from Sabar Taoufik,
*A New Triangle of Numbers: Properties and Observations*, INTEGERS 26 (2026), Article A27.

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
`sum_inv_choose_succ_eq_one_add_sum_sabarNumber`, the alternating sum for harmonic numbers
`sum_sabarNumber_div_succ_eq_harmonic`, and the central-entry formulas
`sabarNumber_central_eq_fineNumber` and `sabarNumber_central_eq_whittGeneralizedCatalan`.

The weighted binomial sum identity `sum_choose_mul_two_pow_add_succ` is proved in
`MathlibExt.Combinatorics.Enumerative.SabarWeightedBinomialSum`, also imported here.

The Fine-number identity `fineNumber_eq_sabarNumber_sub` is proved in
`MathlibExt.Combinatorics.Enumerative.SabarFineNumberDifference`, also imported here.
-/

namespace MetaMathlibExt

@[expose] public section

end

end MetaMathlibExt
