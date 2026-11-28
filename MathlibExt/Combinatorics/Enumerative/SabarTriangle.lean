/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.Combinatorics.Enumerative.WhittGeneralizedCatalan
public import MathlibExt.Combinatorics.FineNumber
import MathlibExt.Combinatorics.Enumerative.FrischReciprocalBinomial
import MathlibExt.Combinatorics.Enumerative.SabarFineNumberWhitt
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Sabar's triangle

Sabar's triangle is `s(n, i) = ∑_{j=i+1}^{n} (-1)^{n-j} C(j, i)` (OEIS A341091 for
`0 ≤ i ≤ n - 1`), from Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*,
INTEGERS 26 (2026), Article A27. This file defines it (`sabarNumber`), checks rows `5` and `10` of
the source's Table 1 and a recurrence in small cases, and proves that for every `n ≥ 2`
`(1 / (n + 1)) ∑_{i=0}^{n} C(n, i)⁻¹ = 1 + ∑_{i=0}^{n-2} (-1)^{n-i-1} s(n-1, i) / ((n-i)(n+1-i))`
(`sum_inv_choose_succ_eq_one_add_sum_sabarNumber`) and the harmonic number identity
`∑_{i=0}^{2n-2} (-1)^i s(2n-1, i) / (i+1) = H_n` (`sum_sabarNumber_div_succ_eq_harmonic`).
It also expresses the central entry `s(2n, n)` in terms of Whitt's generalized Catalan numbers
(`sabarNumber_central_eq_whittGeneralizedCatalan`) and gives three Fine-number formulas for
`s(2n, n)` and one for `s(2n - 1, n)` (`sabarNumber_central_eq_fineNumber`), all for `n ≥ 1`.

## Proof outline

Expanding `s(n - 1, i)` and exchanging the two sums writes the right side as
`1 + ∑_{j=0}^{n-1} ∑_{i=0}^{j-1} (-1)^{j-i} C(j, i) / ((n-i)(n+1-i))`. Completed by its term
`i = j`, the inner sum is an alternating binomial sum of `x ↦ 1 / ((x+1)(x+2))`, and it equals
`1 / ((n+1) C(n, j+1))`: since `1 / ((x+1)(x+2)) = 1 / (2 C(x+2, 2))`, this is the case `c = 2`
of Frisch's identity `MetaMathlibExt.frisch_alternating_reciprocal_binomial`
(`MathlibExt.Combinatorics.Enumerative.FrischReciprocalBinomial`). The completing terms
`1 / ((n-j)(n+1-j))` telescope to `1 - 1 / (n+1)`, and the remaining terms
`1 / ((n+1) C(n, j+1))` for `0 ≤ j ≤ n - 1` are the left side without its term `i = 0`.

For the harmonic identity, the same exchange of sums leaves an alternating binomial sum in each
column. Binomial absorption reduces this inner sum to `(1 - (-1)^j) / (j+1)`, so the even columns
vanish and the odd columns contribute the consecutive reciprocals of `H_n`.

For Theorem 7, complete each central sum with its omitted first term and use Pascal's identity
as in Sabar's induction. Subtracting the central binomial contribution leaves a recurrence with
a Catalan term, which cancels against the consecutive Whitt relation after scaling by `2^(n+1)`.

For Theorem 5, use the central Whitt formula and the Fine–Whitt identity at `n - 1` for `n ≥ 2`.
The Fine–Whitt identity at `n` and the consecutive Whitt relation give `2 F(n) + F(n - 1) = C(n)`,
which converts the even-row formulas using the central binomial coefficients. In a fixed column,
the sums for rows `2n - 1` and `2n` cancel except for the final binomial term. The endpoint `n = 1`
is checked directly.

## References

- Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26 (2026),
  Article A27, pp. 1–17: §2 (the triangle and its adjacent-row identity), Corollary 1,
  Theorems 3 and 5–7, and Corollary 4.
- E. Deutsch and L. Shapiro, *A survey of the Fine numbers*, Discrete Mathematics 241 (2001),
  pp. 241–265 (the Fine numbers as cited in §1 of Sabar Taoufik).
- Milan Janjić, *On Enumeration of Dyck Paths with Colored Hills*, Journal of Integer Sequences
  21 (2018), Article 18.9.7, Identity 35 (the explicit Fine-number formula used at the endpoint).
- Joseph Abate and Ward Whitt, *Brownian Motion and the Generalized Catalan Numbers*,
  Journal of Integer Sequences 14 (2011), Article 11.2.6, §2, equations (9)–(10).
- H. W. Gould and Jocelyn Quaintance, *On the Binomial Identities of Frisch and Klamkin*,
  Journal of Integer Sequences 19 (2016), Article 16.7.7, §1, equation (2) (Frisch's identity).

## Implementation notes

`sabarNumber`, `sabarNumber_rows_five_ten`, `sabarNumber_recurrence_small`,
`sum_inv_choose_succ_eq_one_add_sum_sabarNumber` and `sum_sabarNumber_div_succ_eq_harmonic`
keep the full names, statements and docstrings they had in
`WantedExt.Combinatorics.Enumerative.SabarTriangleWanted`, which imports this module.
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

/-- `∑_{k=0}^{j} (-1)^k C(j, k) / ((y+k+1)(y+k+2)) = 1 / ((y+j+2) C(y+j+1, j+1))`: the case
`b = y + 2`, `c = 2` of Frisch's identity `frisch_alternating_reciprocal_binomial`, since
`1 / C(y+k+2, 2) = 2 / ((y+k+1)(y+k+2))`. -/
private theorem sum_neg_one_pow_mul_choose_mul_one_div (j y : ℕ) :
    ∑ k ∈ Finset.range (j + 1), (-1 : ℚ) ^ k * (j.choose k : ℚ) *
        (1 / (((y + k + 1 : ℕ) : ℚ) * ((y + k + 1 + 1 : ℕ) : ℚ))) =
      1 / (((y + j + 1 + 1 : ℕ) : ℚ) * ((y + j + 1).choose (j + 1) : ℚ)) := by
  have h := frisch_alternating_reciprocal_binomial j (y + 2) 2 two_pos (by omega)
  have hterm : ∀ k, (((y + 2 + k).choose 2 : ℕ) : ℚ)⁻¹ =
      2 * (1 / (((y + k + 1 : ℕ) : ℚ) * ((y + k + 1 + 1 : ℕ) : ℚ))) := fun k => by
    have hk : ((y + k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    rw [show y + 2 + k = y + k + 1 + 1 by omega, Nat.cast_choose_two, Nat.cast_succ (y + k + 1),
      add_sub_cancel_right]
    field_simp
  have hsum : ∑ k ∈ Finset.range (j + 1), (-1 : ℚ) ^ k * (j.choose k : ℚ) *
      (((y + 2 + k).choose 2 : ℕ) : ℚ)⁻¹ =
        2 * ∑ k ∈ Finset.range (j + 1), (-1 : ℚ) ^ k * (j.choose k : ℚ) *
          (1 / (((y + k + 1 : ℕ) : ℚ) * ((y + k + 1 + 1 : ℕ) : ℚ))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [hterm k]; ring
  -- `(j + 2) C(y+j+2, y) = (y+j+2) C(y+j+1, j+1)`.
  have hchoose : ((j + (y + 2)).choose (y + 2 - 2) : ℚ) * ((j : ℚ) + 2) =
      ((y + j + 1 + 1 : ℕ) : ℚ) * ((y + j + 1).choose (j + 1) : ℚ) := by
    rw [show y + 2 - 2 = y by omega, show j + (y + 2) = y + j + 1 + 1 by omega,
      Nat.choose_symm_of_eq_add (show y + j + 1 + 1 = y + (j + 1 + 1) by omega)]
    exact_mod_cast (Nat.add_one_mul_choose_eq (y + j + 1) (j + 1)).symm
  have hc : ((j + (y + 2)).choose (y + 2 - 2) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  rw [hsum] at h
  rw [← hchoose]
  generalize (∑ k ∈ Finset.range (j + 1), (-1 : ℚ) ^ k * (j.choose k : ℚ) *
    (1 / (((y + k + 1 : ℕ) : ℚ) * ((y + k + 1 + 1 : ℕ) : ℚ)))) = S at h ⊢
  generalize (((j + (y + 2)).choose (y + 2 - 2) : ℕ) : ℚ) = C at h hc ⊢
  have hj : (j : ℚ) + 2 ≠ 0 := by positivity
  push_cast at h
  field_simp at h ⊢
  linear_combination h

/-- For `j < n`, `∑_{i=0}^{j} (-1)^{j-i} C(j, i) / ((n-i)(n+1-i)) = 1 / ((n+1) C(n, j+1))`. -/
private theorem sum_neg_one_pow_sub_mul_choose_mul_one_div (n j : ℕ) (hj : j < n) :
    ∑ i ∈ Finset.range (j + 1), (-1 : ℚ) ^ (j - i) * (j.choose i : ℚ) *
        (1 / (((n - i : ℕ) : ℚ) * ((n + 1 - i : ℕ) : ℚ))) =
      1 / (((n + 1 : ℕ) : ℚ) * (n.choose (j + 1) : ℚ)) := by
  obtain ⟨y, rfl⟩ : ∃ y, n = y + j + 1 := ⟨n - j - 1, by omega⟩
  rw [← sum_neg_one_pow_mul_choose_mul_one_div j y, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show j + 1 - 1 - k = j - k by omega, show j - (j - k) = k by omega,
    show y + j + 1 - (j - k) = y + k + 1 by omega,
    show y + j + 1 + 1 - (j - k) = y + k + 1 + 1 by omega, Nat.choose_symm (by omega)]

/-- **Reciprocal binomial sums from Sabar's triangle.** For every natural number $n \ge 2$, the
entries $s(n-1, i)$ of Sabar's triangle satisfy
$$\frac{1}{n+1} \sum_{i=0}^{n} \binom{n}{i}^{-1} =
1 + \sum_{i=0}^{n-2} \frac{(-1)^{n-i-1} \, s(n-1, i)}{(n-i)(n+1-i)}.$$

This is the source's Corollary 1 with the sign used in its proof. As printed, with $(-1)^{n-i}$,
it fails at $n = 2$: the left side is $5/6$ but $1 + s(1, 0)/(2 \cdot 3) = 7/6$.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Corollary 1 (`integers-2026-A27-cor-1`). -/
public theorem sum_inv_choose_succ_eq_one_add_sum_sabarNumber (n : ℕ) (hn : 2 ≤ n) :
    (1 / ((n + 1 : ℕ) : ℚ)) * ∑ i ∈ Finset.range (n + 1), 1 / (n.choose i : ℚ) =
      1 + ∑ i ∈ Finset.range (n - 1),
        (-1 : ℚ) ^ (n - i - 1) * sabarNumber (n - 1) i /
          (((n - i : ℕ) : ℚ) * ((n + 1 - i : ℕ) : ℚ)) := by
  -- Expand `s(n - 1, i)` and absorb the sign `(-1)^(n-i-1)`.
  have hexp : ∀ i ∈ Finset.range (n - 1),
      (-1 : ℚ) ^ (n - i - 1) * (sabarNumber (n - 1) i : ℚ) /
          (((n - i : ℕ) : ℚ) * ((n + 1 - i : ℕ) : ℚ)) =
        ∑ j ∈ Finset.Ioc i (n - 1), (-1 : ℚ) ^ (j - i) * (j.choose i : ℚ) *
          (1 / (((n - i : ℕ) : ℚ) * ((n + 1 - i : ℕ) : ℚ))) := by
    intro i _
    simp only [sabarNumber]
    push_cast
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ioc] at hj
    have hsq : (-1 : ℚ) ^ (n - 1 - j) * (-1) ^ (n - 1 - j) = 1 := by
      rw [← mul_pow]
      norm_num
    rw [show n - i - 1 = (j - i) + (n - 1 - j) by omega, pow_add, div_eq_mul_one_div]
    linear_combination ((-1 : ℚ) ^ (j - i) * (j.choose i : ℚ) *
      (1 / (((n - i : ℕ) : ℚ) * ((n + 1 - i : ℕ) : ℚ)))) * hsq
  -- Exchange the sums: `i < j ≤ n - 1`.
  rw [Finset.sum_congr rfl hexp,
    Finset.sum_comm' (t' := Finset.range n) (s' := fun j => Finset.range j) (by
      intro i j
      simp only [Finset.mem_range, Finset.mem_Ioc]
      omega)]
  -- Each inner sum is a Beta value minus its missing term `i = j`.
  have hinner : ∀ j ∈ Finset.range n,
      ∑ i ∈ Finset.range j, (-1 : ℚ) ^ (j - i) * (j.choose i : ℚ) *
          (1 / (((n - i : ℕ) : ℚ) * ((n + 1 - i : ℕ) : ℚ))) =
        1 / (((n + 1 : ℕ) : ℚ) * (n.choose (j + 1) : ℚ)) -
          1 / (((n - j : ℕ) : ℚ) * ((n + 1 - j : ℕ) : ℚ)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [← sum_neg_one_pow_sub_mul_choose_mul_one_div n j hj, Finset.sum_range_succ]
    simp
  -- The missing terms telescope.
  have htel : ∑ j ∈ Finset.range n, 1 / (((n - j : ℕ) : ℚ) * ((n + 1 - j : ℕ) : ℚ)) =
      1 - 1 / ((n + 1 : ℕ) : ℚ) := by
    have h := Finset.sum_range_sub (fun j => 1 / ((n + 1 - j : ℕ) : ℚ)) n
    rw [show n + 1 - n = 1 by omega, Nat.sub_zero, Nat.cast_one, div_one] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hpos : ((n - j : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [show n + 1 - (j + 1) = n - j by omega, show n + 1 - j = n - j + 1 by omega]
    push_cast
    field_simp
    ring
  have hbeta : ∑ j ∈ Finset.range n, 1 / (((n + 1 : ℕ) : ℚ) * (n.choose (j + 1) : ℚ)) =
      1 / ((n + 1 : ℕ) : ℚ) * ∑ j ∈ Finset.range n, 1 / (n.choose (j + 1) : ℚ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => (one_div_mul_one_div _ _).symm
  rw [Finset.sum_congr rfl hinner, Finset.sum_sub_distrib, htel, hbeta, Finset.sum_range_succ',
    Nat.choose_zero_right, Nat.cast_one, div_one]
  ring

/-- Strip the constant term from the alternating binomial sum of row `j + 1`,
then use binomial absorption to account for the denominator `i + 1`. -/
private theorem sum_neg_one_pow_mul_choose_div_succ (j : ℕ) :
    ∑ i ∈ Finset.range j, (-1 : ℚ) ^ i * (j.choose i : ℚ) / ((i + 1 : ℕ) : ℚ) =
      (1 - (-1) ^ j) / ((j + 1 : ℕ) : ℚ) := by
  have hrow : ∑ i ∈ Finset.range (j + 1), (-1 : ℚ) ^ i * ((j + 1).choose i : ℚ) =
      (-1 : ℚ) ^ j := by
    exact_mod_cast (show ∑ i ∈ Finset.range (j + 1), (-1 : ℤ) ^ i * ((j + 1).choose i : ℤ) =
      (-1 : ℤ) ^ j by simpa using Int.alternating_sum_range_choose_eq_choose (n := j) (m := j))
  rw [Finset.sum_range_succ'] at hrow
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, pow_succ, mul_neg, mul_one,
    neg_mul, Finset.sum_neg_distrib] at hrow
  calc
    _ = (∑ i ∈ Finset.range j, (-1 : ℚ) ^ i * ((j + 1).choose (i + 1) : ℚ)) /
          ((j + 1 : ℕ) : ℚ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [mul_div_assoc]
      congr 1
      apply (div_eq_div_iff (by positivity) (by positivity)).2
      exact_mod_cast (Nat.mul_comm _ _).trans (Nat.add_one_mul_choose_eq j i)
    _ = _ := by
      congr 1
      linear_combination -hrow

/-- **The harmonic numbers as an alternating sum of Sabar numbers.** For every natural number
$n \ge 2$, writing $s(m, i)$ for Sabar's triangle and $H_n = \sum_{j=1}^{n} 1/j$ for the $n$-th
harmonic number, in the rational numbers

$$\sum_{i=0}^{2n-2} \frac{(-1)^i \, s(2n-1, i)}{i+1} = H_n.$$

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Theorem 3 (`integers-2026-A27-thm-3`). -/
public theorem sum_sabarNumber_div_succ_eq_harmonic (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ Finset.range (2 * n - 1), (-1 : ℚ) ^ i * sabarNumber (2 * n - 1) i / ((i + 1 : ℕ) : ℚ) =
      harmonic n := by
  let N := 2 * n - 1
  change ∑ i ∈ Finset.range N, (-1 : ℚ) ^ i * sabarNumber N i / ((i + 1 : ℕ) : ℚ) = harmonic n
  have hN : N + 1 = 2 * n := by dsimp [N]; omega
  -- Expand Sabar's triangle and exchange the sums over `i < j ≤ N`.
  have hexpand (i : ℕ) :
      (-1 : ℚ) ^ i * sabarNumber N i / ((i + 1 : ℕ) : ℚ) =
        ∑ j ∈ Finset.Ioc i N, (-1 : ℚ) ^ (N - j) *
          ((-1 : ℚ) ^ i * (j.choose i : ℚ) / ((i + 1 : ℕ) : ℚ)) := by
    simp only [sabarNumber]
    push_cast
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_div_assoc, mul_left_comm]
  rw [Finset.sum_congr rfl (fun i _ => hexpand i),
    Finset.sum_comm' (t' := Finset.range (N + 1)) (s' := Finset.range) (by
      intro i j
      simp only [Finset.mem_range, Finset.mem_Ioc]
      omega)]
  simp_rw [← Finset.mul_sum, sum_neg_one_pow_mul_choose_div_succ]
  -- Pair each even index `2*k` (zero) with the odd index `2*k+1` (the reciprocal of `k+1`).
  have hpair (f : ℕ → ℚ) (m : ℕ) :
      ∑ j ∈ Finset.range (2 * m), f j =
        ∑ k ∈ Finset.range m, (f (2 * k) + f (2 * k + 1)) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, Finset.sum_range_succ, add_assoc]
  rw [hN, hpair]
  unfold harmonic
  refine Finset.sum_congr rfl fun k _ => ?_
  have heven : (-1 : ℚ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
  have hodd : (-1 : ℚ) ^ (2 * k + 1) = -1 := by simp [pow_succ, heven]
  have hsign : (-1 : ℚ) ^ (N - (2 * k + 1)) = 1 := by
    rw [show N - (2 * k + 1) = 2 * (n - (k + 1)) by omega, pow_mul]
    norm_num
  simp only [heven, hodd, hsign, sub_self, zero_div, mul_zero, one_mul, zero_add]
  push_cast
  rw [← one_div]
  field_simp
  ring

-- Include the term at the bottom of the column, which `sabarNumber` omits.
private def alternatingColumn (k m : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (m + 1), (-1 : ℚ) ^ (m - j) * ((k + j).choose k : ℚ)

private lemma alternatingColumn_succ (k m : ℕ) :
    alternatingColumn k (m + 1) = ((k + (m + 1)).choose k : ℚ) - alternatingColumn k m := by
  simp only [alternatingColumn, Finset.sum_range_succ _ (m + 1), Nat.sub_self, pow_zero, one_mul]
  rw [sub_eq_neg_add, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [show m + 1 - j = m - j + 1 by omega, pow_succ, mul_neg_one, neg_mul]

-- Summing Pascal's identity leaves the last coefficient and the previous column.
private lemma two_mul_alternatingColumn_succ (k m : ℕ) :
    2 * alternatingColumn (k + 1) m = ((k + 1 + m).choose (k + 1) : ℚ) + alternatingColumn k m := by
  induction m with
  | zero => norm_num [alternatingColumn]
  | succ m ih =>
    rw [alternatingColumn_succ, alternatingColumn_succ k,
      Nat.add_right_comm k 1 (m + 1), Nat.choose_succ_succ',
      show k + (m + 1) = k + 1 + m by omega]
    push_cast
    linear_combination -ih

private lemma alternatingColumn_diag (n : ℕ) :
    alternatingColumn n n = (sabarNumber (2 * n) n : ℚ) + (-1) ^ n := by
  unfold alternatingColumn sabarNumber
  push_cast
  have hIoc : Finset.Ioc n (2 * n) = Finset.Ico (n + 1) (2 * n + 1) := by
    ext j
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [Finset.sum_range_succ', hIoc, Finset.sum_Ico_eq_sum_range,
    show 2 * n + 1 - (n + 1) = n by omega]
  simp only [Nat.sub_zero, Nat.add_zero, Nat.choose_self, Nat.cast_one, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show n + (j + 1) = n + 1 + j by omega,
    show 2 * n - (n + 1 + j) = n - (j + 1) by omega]

private def centralColumnDifference (n : ℕ) : ℚ :=
  3 * alternatingColumn n n - 2 * ((2 * n).choose n : ℚ)

-- After subtracting the central binomial terms, Sabar's recurrence has Catalan forcing.
private lemma centralColumnDifference_succ (n : ℕ) :
    2 * centralColumnDifference (n + 1) + centralColumnDifference n = -(catalan n : ℚ) := by
  have hcolumn := two_mul_alternatingColumn_succ n (n + 1)
  rw [alternatingColumn_succ n, show n + 1 + (n + 1) = 2 * (n + 1) by omega,
    show n + (n + 1) = 2 * n + 1 by omega] at hcolumn
  have hmiddle : ((2 * (n + 1)).choose (n + 1) : ℚ) = 2 * ((2 * n + 1).choose n : ℚ) := by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, Nat.choose_succ_succ', Nat.choose_symm_half,
      Nat.cast_add, two_mul ((2 * n + 1).choose n : ℚ)]
  have hnear : ((2 * n + 1).choose n : ℚ) + catalan n = 2 * ((2 * n).choose n : ℚ) := by
    have habsorb := Nat.choose_mul_succ_eq (2 * n) n
    rw [show 2 * n + 1 - n = n + 1 by omega] at habsorb
    have hchoose := congrArg (fun t : ℕ => (t : ℚ)) habsorb
    have hcatalan := congrArg (fun t : ℕ => (t : ℚ)) (succ_mul_catalan_eq_centralBinom n)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.centralBinom]
      at hchoose hcatalan
    apply mul_left_cancel₀ (show (n : ℚ) + 1 ≠ 0 by positivity)
    linear_combination hcatalan - hchoose
  unfold centralColumnDifference
  linear_combination 3 * hcolumn - hmiddle + hnear

/-- **Central entries of Sabar's triangle and Whitt's numbers.** Let $C(2, m)$ denote Whitt's
generalized Catalan numbers at $\alpha = 2$. For every natural number $n \ge 1$, the central
entry $s(2n, n)$ of Sabar's triangle satisfies
$$s(2n, n) = \frac{2}{3} \binom{2n}{n} - \frac{1}{3} \cdot \frac{C(2, n)}{2^{n+1}} +
(-1)^{n+1} + \frac{(-1)^n}{2^{n+1}}.$$

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Theorem 7 (`integers-2026-A27-thm-7`). -/
public theorem sabarNumber_central_eq_whittGeneralizedCatalan (n : ℕ) (hn : 1 ≤ n) :
    (sabarNumber (2 * n) n : ℚ) =
      (2 / 3) * ((2 * n).choose n : ℚ) - (1 / 3) * whittGeneralizedCatalan 2 n / 2 ^ (n + 1) +
        (-1) ^ (n + 1) + (-1) ^ n / 2 ^ (n + 1) := by
  -- The scaled difference and Whitt's numbers have opposite Catalan terms.
  have hscaled (m : ℕ) (hm : 1 ≤ m) :
      2 ^ (m + 1) * centralColumnDifference m = 3 * (-1) ^ m - whittGeneralizedCatalan 2 m := by
    induction m, hm using Nat.le_induction with
    | base => decide +kernel
    | succ m hm ih =>
      rw [pow_succ (2 : ℚ) (m + 1), pow_succ (-1 : ℚ) m]
      linear_combination (2 : ℚ) ^ (m + 1) * centralColumnDifference_succ m - ih +
        whittGeneralizedCatalan_two_add_succ m hm
  have h := hscaled n hn
  rw [centralColumnDifference, alternatingColumn_diag] at h
  rw [pow_succ (-1 : ℚ) n]
  field_simp
  linear_combination h

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
public theorem sabarNumber_central_eq_fineNumber (n : ℕ) (hn : 1 ≤ n) :
    (sabarNumber (2 * n) n : ℚ) =
        (1 / 6) * ((2 * n + 2).choose (n + 1) : ℚ) + (2 / 3) * fineNumber n + (-1) ^ (n + 1) ∧
      (sabarNumber (2 * n) n : ℚ) =
        (1 / 3) * (2 * n + 1) * (catalan n : ℚ) + (2 / 3) * fineNumber n + (-1) ^ (n + 1) ∧
      (sabarNumber (2 * n) n : ℚ) =
        (2 / 3) * ((2 * n).choose n : ℚ) - (1 / 3) * fineNumber (n - 1) + (-1) ^ (n + 1) ∧
      (sabarNumber (2 * n - 1) n : ℚ) =
        (2 / 3) * ((2 * n - 1).choose n : ℚ) + (1 / 3) * fineNumber (n - 1) + (-1) ^ n := by
  by_cases h : n = 1
  · subst n
    simp only [fineNumber_eq_sum]
    decide +kernel
  have hprev := two_pow_mul_fineNumber_eq_whittGeneralizedCatalan (n - 1) (by omega)
  rw [show n - 1 + 2 = n + 1 by omega, Nat.sub_add_cancel hn] at hprev
  have hsign : (-1 : ℚ) ^ n = -(-1) ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ, mul_neg_one]
  have hwhitt : whittGeneralizedCatalan 2 n = 2 ^ (n + 1) * fineNumber (n - 1) + 3 * (-1) ^ n := by
    rw [hsign]
    linear_combination -hprev
  have hthird : (sabarNumber (2 * n) n : ℚ) =
      (2 / 3) * ((2 * n).choose n : ℚ) - (1 / 3) * fineNumber (n - 1) + (-1) ^ (n + 1) := by
    rw [sabarNumber_central_eq_whittGeneralizedCatalan n hn, hwhitt]
    field_simp
    ring
  -- The signs in the two consecutive Fine–Whitt identities cancel.
  have hfine : 2 * fineNumber n + fineNumber (n - 1) = catalan n := by
    have hcurr := two_pow_mul_fineNumber_eq_whittGeneralizedCatalan n hn
    rw [pow_succ (2 : ℚ) (n + 1)] at hcurr
    apply mul_left_cancel₀ (pow_ne_zero (n + 1) (show (2 : ℚ) ≠ 0 by norm_num))
    linear_combination hcurr + whittGeneralizedCatalan_two_add_succ n hn - hwhitt
  have hcatalan : ((2 * n).choose n : ℚ) = ((n : ℚ) + 1) * catalan n := by
    exact_mod_cast (succ_mul_catalan_eq_centralBinom n).symm
  have hnext : ((2 * n + 2).choose (n + 1) : ℚ) =
      2 * (2 * (n : ℚ) + 1) * catalan n := by
    have hbinom : ((n : ℚ) + 1) * ((2 * n + 2).choose (n + 1) : ℚ) =
        2 * (2 * (n : ℚ) + 1) * ((2 * n).choose n : ℚ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    rw [hcatalan] at hbinom
    apply mul_left_cancel₀ (show (n : ℚ) + 1 ≠ 0 by positivity)
    linear_combination hbinom
  have hsecond : (sabarNumber (2 * n) n : ℚ) =
      (1 / 3) * (2 * n + 1) * (catalan n : ℚ) + (2 / 3) * fineNumber n + (-1) ^ (n + 1) := by
    rw [hthird, hcatalan]
    linear_combination -(1 / 3) * hfine
  refine ⟨?_, hsecond, hthird, ?_⟩
  · rw [hsecond, hnext]
    ring
  -- Adding the two consecutive rows in the same column cancels all but the last term.
  have hrow : (sabarNumber (2 * n) n : ℚ) =
      ((2 * n).choose n : ℚ) - sabarNumber (2 * n - 1) n := by
    simp only [sabarNumber]
    push_cast
    have htop := Finset.sum_Ioc_succ_top (show n ≤ 2 * n - 1 by omega)
      (fun j => (-1 : ℚ) ^ (2 * n - j) * (j.choose n : ℚ))
    rw [show 2 * n - 1 + 1 = 2 * n by omega] at htop
    rw [htop, Nat.sub_self, pow_zero, one_mul, sub_eq_neg_add, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ioc] at hj
    rw [show 2 * n - j = (2 * n - 1 - j) + 1 by omega, pow_succ, mul_neg_one, neg_mul]
  have hmiddle : ((2 * n).choose n : ℚ) = 2 * ((2 * n - 1).choose n : ℚ) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, Nat.add_sub_cancel,
      Nat.choose_succ_succ', Nat.choose_symm_half, Nat.cast_add, ← two_mul]
  rw [pow_succ (-1 : ℚ) n, mul_neg_one] at hthird
  linear_combination hrow - hthird + (1 / 3) * hmiddle

end

end MetaMathlibExt
