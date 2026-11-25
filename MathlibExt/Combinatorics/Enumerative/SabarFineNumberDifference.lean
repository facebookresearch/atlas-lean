/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.SabarTriangle
public import MathlibExt.Combinatorics.FineNumber
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fine numbers as a difference of two entries of Sabar's triangle

This file proves that for every `n ≥ 2` the Fine number `F(n)` is the difference
`s(2n, n+1) - s(2n, n-1)` of two entries of row `2n` of Sabar's triangle
(`fineNumber_eq_sabarNumber_sub`), from Sabar Taoufik, *A New Triangle of Numbers: Properties
and Observations*, INTEGERS 26 (2026), Article A27, Theorem 4.

## Proof outline

Write `R(r, m) = ∑_{k=0}^{m} (-2)^(m-k) C(r, k)` for the partial sums of binomial row `r`
weighted by powers of `-2`, so that `R(r, m + 1) = -2 R(r, m) + C(r, m + 1)`, and Pascal's rule
gives `R(r + 1, m + 1) = C(r, m + 1) - R(r, m)`. Removing the top term of the alternating sum
defining `s` gives the same recursion `s(N + 1, m) = C(N + 1, m) - s(N, m)` for `m ≤ N`, so by
induction on `N - m`, `s(N, m) + (-1)^(N-m) = R(N + 1, N - m)` for `m ≤ N`. On the other side,
the factor `(i + 1) / (n + 1)` in the definition of `F(n)` makes it the difference
`F(n) = 2 R(2n + 1, n) - R(2n + 2, n)`. With `r = 2n + 1`, both sides of the identity equal
`R(r, n - 1) + 2 R(r, n) - C(r, n)`, by the two recursions of `R` and `C(r, n + 1) = C(r, n)`.

The rewriting of `F(n)` follows the proof of the alternating formula
`fineNumber_eq_half_neg_one_pow_add_sum` in `MathlibExt.Combinatorics.Enumerative.SabarFineNumber`,
whose helper lemmas are private to that file.

## Implementation notes

`fineNumber_eq_sabarNumber_sub` keeps the full name, statement and docstring it had in
`WantedExt.Combinatorics.Enumerative.SabarTriangleWanted`, which imports this module.
-/

namespace MetaMathlibExt

namespace fineNumber_eq_sabarNumber_sub

/-- The partial sum `R(r, m) = ∑_{k=0}^{m} (-2)^(m-k) C(r, k)` of binomial row `r`. -/
private def rowSum (r m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (m + 1), (-2 : ℚ) ^ (m - k) * (r.choose k : ℚ)

private lemma rowSum_zero (r : ℕ) : rowSum r 0 = 1 := by
  simp [rowSum]

private lemma rowSum_succ (r m : ℕ) :
    rowSum r (m + 1) = -2 * rowSum r m + r.choose (m + 1) := by
  rw [rowSum, Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul, rowSum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [show m + 1 - k = m - k + 1 by have := Finset.mem_range.mp hk; omega, pow_succ]
  ring

-- Pascal's rule gives the recursion of Sabar's triangle along the diagonals of `R`.
private lemma rowSum_succ_succ (r m : ℕ) :
    rowSum (r + 1) (m + 1) = r.choose (m + 1) - rowSum r m := by
  induction m with
  | zero => simp [rowSum, Finset.sum_range_succ]; ring
  | succ m ih =>
    rw [rowSum_succ, ih, rowSum_succ r m, Nat.choose_succ_succ' r (m + 1)]
    push_cast
    ring

-- Removing the top term `j = m + d + 1` of the alternating sum changes the sign of the others.
private lemma sabarNumber_add_succ (m d : ℕ) :
    sabarNumber (m + d + 1) m = ((m + d + 1).choose m : ℤ) - sabarNumber (m + d) m := by
  unfold sabarNumber
  rw [Finset.sum_Ioc_succ_top (by omega), Nat.sub_self, pow_zero, one_mul, add_comm,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Ioc] at hj
  rw [show m + d + 1 - j = m + d - j + 1 by omega, pow_succ]
  ring

private lemma sabarNumber_add_add_neg_one_pow (m d : ℕ) :
    (sabarNumber (m + d) m : ℚ) + (-1) ^ d = rowSum (m + d + 1) d := by
  induction d with
  | zero => simp [sabarNumber, rowSum_zero]
  | succ d ih =>
    rw [← add_assoc, sabarNumber_add_succ, rowSum_succ_succ, ← ih,
      show m + d + 1 = m + (d + 1) by omega, Nat.choose_symm_add]
    push_cast
    ring

/-- The closed form `s(N, m) + (-1)^(N-m) = R(N + 1, N - m)` for `m ≤ N`. -/
private lemma sabarNumber_add_neg_one_pow (N m : ℕ) (h : m ≤ N) :
    (sabarNumber N m : ℚ) + (-1) ^ (N - m) = rowSum (N + 1) (N - m) := by
  obtain ⟨d, rfl⟩ : ∃ d, N = m + d := ⟨N - m, by omega⟩
  rw [Nat.add_sub_cancel_left]
  exact sabarNumber_add_add_neg_one_pow m d

-- The factor `(i + 1) / (n + 1)` in the definition of the Fine number gives a difference of rows.
private lemma fineNumber_eq_rowSum_sub (n : ℕ) :
    fineNumber n = 2 * rowSum (2 * n + 1) n - rowSum (2 * n + 1 + 1) n := by
  rw [fineNumber_eq_sum, ← Finset.sum_range_reflect]
  simp only [rowSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by simpa using Finset.mem_range.mp hk
  simp only [Nat.add_sub_cancel, Nat.sub_sub_self hk', Nat.cast_sub hk']
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
  have hchoose := congrArg (fun t : ℕ => (t : ℚ)) (Nat.choose_mul_succ_eq (2 * n + 1) k)
  push_cast [Nat.cast_sub (show k ≤ 2 * n + 1 + 1 by omega)] at hchoose
  field_simp [show (n : ℚ) + 1 ≠ 0 by positivity]
  linear_combination -hchoose

end fineNumber_eq_sabarNumber_sub

open fineNumber_eq_sabarNumber_sub

/-- **Fine numbers from Sabar's triangle.** For every natural number $n \ge 2$, the Fine number
$F(n)$ is the difference of two entries of row $2n$ of Sabar's triangle $s$:
$F(n) = s(2n, n+1) - s(2n, n-1)$.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Theorem 4 (`integers-2026-A27-thm-4`). -/
public theorem fineNumber_eq_sabarNumber_sub (n : ℕ) (hn : 2 ≤ n) :
    fineNumber n = (sabarNumber (2 * n) (n + 1) - sabarNumber (2 * n) (n - 1) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  -- With `r = 2n + 1`: `s(2n, n+1) + (-1)^(n-1) = R(r, n-1)` and
  -- `s(2n, n-1) + (-1)^(n+1) = R(r, n+1)`.
  have h₁ := sabarNumber_add_neg_one_pow (2 * (k + 1)) (k + 1 + 1) (by omega)
  have h₂ := sabarNumber_add_neg_one_pow (2 * (k + 1)) k (by omega)
  rw [show 2 * (k + 1) - (k + 1 + 1) = k by omega] at h₁
  rw [show 2 * (k + 1) - k = k + 1 + 1 by omega] at h₂
  -- `F(n) = 2 R(r, n) - R(r + 1, n)`, `R(r + 1, n) = C(r, n) - R(r, n-1)` and
  -- `R(r, n+1) = -2 R(r, n) + C(r, n+1)`.
  have hF := fineNumber_eq_rowSum_sub (k + 1)
  have he := rowSum_succ_succ (2 * (k + 1) + 1) k
  have hc := rowSum_succ (2 * (k + 1) + 1) (k + 1)
  have hsymm : ((2 * (k + 1) + 1).choose (k + 1) : ℚ) =
      ((2 * (k + 1) + 1).choose (k + 1 + 1) : ℚ) := by
    rw [Nat.choose_symm_half]
  have hsign : (-1 : ℚ) ^ (k + 1 + 1) = (-1) ^ k := by ring
  rw [Nat.add_sub_cancel]
  push_cast
  linear_combination hF - h₁ + h₂ - he + hc - hsymm - hsign

end MetaMathlibExt
