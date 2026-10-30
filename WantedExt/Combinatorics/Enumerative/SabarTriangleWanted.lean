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

/-- Sabar's triangle: `s(n, i) = ∑_{j=i+1}^{n} (-1)^{n-j} C(j, i)`, the number of the paper's
grid paths (OEIS A341091 for `0 ≤ i ≤ n - 1`; it is `0` for `i ≥ n`).

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Section 2 (definition of `s(n, i)`). -/
public def sabarNumber (n i : ℕ) : ℤ :=
  ∑ j ∈ Finset.Ioc i n, (-1) ^ (n - j) * (j.choose i : ℤ)

/-- Characteristic values: rows `n = 5` (`1, 2, 7, 6, 5`) and `n = 10` (`0, 6, 24, 71, 129, 167,
147, 92, 36, 10`) of Table 1.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Table 1. -/
public theorem sabarNumber_rows_five_ten :
    (List.range 5).map (sabarNumber 5) = [1, 2, 7, 6, 5] ∧
      (List.range 10).map (sabarNumber 10) = [0, 6, 24, 71, 129, 167, 147, 92, 36, 10] := by
  decide +kernel

/-- The recurrence `s(n + 2, i + 1) = s(n, i + 1) + C(n + 1, i)` (the paper's third basic
identity `s(n, i) = s(n-2, i) + C(n-1, i-1)`), checked for `i < n < 8`; it fails for
`i ≥ n`, e.g. `s(2, 1) = 2` but `s(0, 1) + C(1, 0) = 1`.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Section 2 (identities following from the definition). -/
public theorem sabarNumber_recurrence_small :
    ∀ n < 8, ∀ i < n,
      sabarNumber (n + 2) (i + 1) = sabarNumber n (i + 1) + ((n + 1).choose i : ℤ) := by
  decide +kernel

/-- Theorem 2: for `n ≥ 2`,
`H_n = C_n + ∑_{i=0}^{n-2} (-1)^{n-i} s(n-1, i) / (n - i)`, where
`C_n = (1/n) ∑_{i=0}^{n-1} C(n-1, i)⁻¹`.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Theorem 2 (`integers-2026-A27-thm-2`). -/
public theorem_wanted harmonic_eq_sum_inv_choose_add_sum_sabarNumber (n : ℕ) (hn : 2 ≤ n) :
    harmonic n =
      (1 / (n : ℚ)) * ∑ i ∈ Finset.range n, 1 / ((n - 1).choose i : ℚ) +
        ∑ i ∈ Finset.range (n - 1), (-1 : ℚ) ^ (n - i) * sabarNumber (n - 1) i / ((n - i : ℕ) : ℚ)

/-- Corollary 1, with the sign of the paper's proof: for `n ≥ 2`,
`C_{n+1} = 1 + ∑_{i=0}^{n-2} (-1)^{n-i-1} s(n-1, i) / ((n-i)(n+1-i))`. As printed, with
`(-1)^{n-i}`, it fails at `n = 2`: `C_3 = 5/6` but `1 + s(1, 0)/(2·3) = 7/6`.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Corollary 1 (`integers-2026-A27-cor-1`). -/
public theorem_wanted sum_inv_choose_succ_eq_one_add_sum_sabarNumber (n : ℕ) (hn : 2 ≤ n) :
    (1 / ((n + 1 : ℕ) : ℚ)) * ∑ i ∈ Finset.range (n + 1), 1 / (n.choose i : ℚ) =
      1 + ∑ i ∈ Finset.range (n - 1),
        (-1 : ℚ) ^ (n - i - 1) * sabarNumber (n - 1) i / (((n - i : ℕ) : ℚ) * ((n + 1 - i : ℕ) : ℚ))

/-- Theorem 3: for `n ≥ 2`, `∑_{i=0}^{2n-2} (-1)^i s(2n-1, i) / (i + 1) = H_n`.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Theorem 3 (`integers-2026-A27-thm-3`). -/
public theorem_wanted sum_sabarNumber_div_succ_eq_harmonic (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ Finset.range (2 * n - 1), (-1 : ℚ) ^ i * sabarNumber (2 * n - 1) i / ((i + 1 : ℕ) : ℚ) =
      harmonic n

/-- Theorem 4: for `n ≥ 2`, `f_n = s(2n, n+1) - s(2n, n-1)`.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Theorem 4 (`integers-2026-A27-thm-4`). -/
public theorem_wanted fineNumber_eq_sabarNumber_sub (n : ℕ) (hn : 2 ≤ n) :
    fineNumber n = (sabarNumber (2 * n) (n + 1) - sabarNumber (2 * n) (n - 1) : ℤ)

/-- Corollary 2: for `n ≥ 2`,
`∑_{k=1}^{n} (-1)^{k+1} (1 - 2k/(n+1) + n/(k+1)) C(n+k, k) = n`.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Corollary 2 (`integers-2026-A27-cor-2`). -/
public theorem_wanted sum_neg_one_pow_mul_choose_eq_self (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, (-1 : ℚ) ^ (k + 1) *
        (1 - 2 * (k : ℚ) / (n + 1) + (n : ℚ) / (k + 1)) * ((n + k).choose k : ℚ) = n

/-- Corollary 3: for `n ≥ 2`,
`f_n = (1/2)(-1)^n + (1/2) ∑_{k=0}^{n} (-1)^{n-k} (1 - n/(k+1)) C(n+k, k)`.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Corollary 3 (`integers-2026-A27-cor-3`). -/
public theorem_wanted fineNumber_eq_half_neg_one_pow_add_sum (n : ℕ) (hn : 2 ≤ n) :
    fineNumber n = (1 / 2) * (-1 : ℚ) ^ n +
      (1 / 2) * ∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (n - k) * (1 - (n : ℚ) / (k + 1)) * ((n + k).choose k : ℚ)

/-- Theorem 5: for `n ≥ 1`, the central coefficients
`s(2n, n) = (1/6) C(2n+2, n+1) + (2/3) f_n + (-1)^{n+1} = (1/3)(2n+1) C(n) + (2/3) f_n + (-1)^{n+1}
= (2/3) C(2n, n) - (1/3) f_{n-1} + (-1)^{n+1}`, and consequently
`s(2n-1, n) = (2/3) C(2n-1, n) + (1/3) f_{n-1} + (-1)^n`; all four as a conjunction.

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

/-- Lemma 1: for `n ≥ 1`, `V_n(2) + V_{n+1}(2) = 3 · 2^n C(2n+2, n+1)`, where
`V_n(α) = ∑_{k=0}^{n} C(n+k, k) α^k`.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Lemma 1 (`integers-2026-A27-lem-1`). -/
public theorem_wanted sum_choose_mul_two_pow_add_succ (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (n + k).choose k * 2 ^ k +
        ∑ k ∈ Finset.range (n + 2), (n + 1 + k).choose k * 2 ^ k =
      3 * 2 ^ n * (2 * n + 2).choose (n + 1)

/-- Theorem 6: for `n ≥ 1`, `C(2, n) + C(2, n+1) = 2^{n+1} C(n)`.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Theorem 6 (`integers-2026-A27-thm-6`). -/
public theorem_wanted whittGeneralizedCatalan_two_add_succ (n : ℕ) (hn : 1 ≤ n) :
    whittGeneralizedCatalan 2 n + whittGeneralizedCatalan 2 (n + 1) = 2 ^ (n + 1) * catalan n

/-- Theorem 7: for `n ≥ 1`,
`s(2n, n) = (2/3) C(2n, n) - (1/3) C(2, n) / 2^{n+1} + (-1)^{n+1} + (-1)^n / 2^{n+1}`.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Theorem 7 (`integers-2026-A27-thm-7`). -/
public theorem_wanted sabarNumber_central_eq_whittGeneralizedCatalan (n : ℕ) (hn : 1 ≤ n) :
    (sabarNumber (2 * n) n : ℚ) =
      (2 / 3) * ((2 * n).choose n : ℚ) - (1 / 3) * whittGeneralizedCatalan 2 n / 2 ^ (n + 1) +
        (-1) ^ (n + 1) + (-1) ^ n / 2 ^ (n + 1)

/-- Corollary 4: for `n ≥ 1`, `2^{n+2} f_n = C(2, n+1) + 3 (-1)^n`.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Corollary 4 (`integers-2026-A27-cor-4`). -/
public theorem_wanted two_pow_mul_fineNumber_eq_whittGeneralizedCatalan (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (n + 2) * fineNumber n = whittGeneralizedCatalan 2 (n + 1) + 3 * (-1) ^ n

end

end MetaMathlibExt
