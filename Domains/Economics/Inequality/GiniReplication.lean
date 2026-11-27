/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Economics.Inequality.Gini
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Replication of an income distribution

A copy of person `i` has index `(i, r)` and still earns `x i`. Thus making `k` copies of
every person multiplies total income by `k`, but counts every ordered pair of original
people `k²` times. These factors cancel in the population Gini, not in general in its
finite-sample correction. In contrast, changing the unit of income leaves *both* unchanged.

## References

* L. G. Bellù and P. Liberati, *Policy Impacts on Inequality: Inequality and Axioms for its
  Measurement*, [FAO EASYPol Module 054](https://www.fao.org/4/am340e/am340e.pdf) (2006),
  §§3.3.2 and 3.3.4 (scale invariance and the population principle); §4 illustrates both for
  the Gini index. The finite-sample comparison below is a deduction from the two normalizations.
-/

namespace MathlibExt.Economics.Inequality

open Finset

variable {ι : Type*} [Fintype ι]

/-- For a finite population of size `n` with real incomes `x`, making `k ≥ 1` copies of
 each person leaves the population Gini unchanged: `gini (fun (i, r) ↦ x i) = gini x` on
 `ι × Fin k`. The ordered-pair sum of absolute income differences grows by a factor `k²`,
 as does its denominator `2 * n * ∑ i, x i`. For `n ≥ 1`, nonnegative incomes and positive
 mean `μ`, this denominator is `2 n² μ`; the algebraic identity itself requires no sign
 condition or nonemptiness, and division by zero gives zero. -/
theorem gini_replicate (x : ι → ℝ) {k : ℕ} (hk : 0 < k) :
    gini (fun p : ι × Fin k => x p.1) = gini x := by
  have htotal : (∑ p : ι × Fin k, x p.1) = k * ∑ i, x i := by
    simp [Fintype.sum_prod_type, nsmul_eq_mul, Finset.mul_sum]
  have hnum : (∑ p : ι × Fin k, ∑ q : ι × Fin k, |x p.1 - x q.1|) =
      (k : ℝ) ^ 2 * ∑ i, ∑ j, |x i - x j| := by
    simp [Fintype.sum_prod_type, nsmul_eq_mul, Finset.mul_sum, sq, mul_assoc]
  have hden : 2 * (Fintype.card (ι × Fin k) : ℝ) * (∑ p : ι × Fin k, x p.1) =
      (k : ℝ) ^ 2 * (2 * Fintype.card ι * ∑ i, x i) := by
    rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, htotal]
    ring
  unfold gini
  rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero 2 (Nat.cast_ne_zero.mpr hk.ne'))]

/-- The bias-corrected Gini for `n ≥ 2` real incomes `x` is the sum of `|x i - x j|` over
 all ordered pairs divided by `2 * (n - 1) * ∑ i, x i`, where `n` is the population size.
 For nonnegative incomes with positive mean `μ`, the denominator is `2 n (n - 1) μ`.
 The formula takes the value zero at total income zero (division by zero in `ℝ`). -/
noncomputable def biasCorrectedGini (x : ι → ℝ) (_hn : 2 ≤ Fintype.card ι) : ℝ :=
  (∑ i, ∑ j, |x i - x j|) / (2 * ((Fintype.card ι : ℝ) - 1) * ∑ i, x i)

/-- For any finite population of `n ≥ 2` real incomes `x`, the bias-corrected Gini is
 `n / (n - 1)` times the population Gini: their ordered-pair numerators are the same and
 their denominators are `2 (n - 1) ∑ i, x i` and `2 n ∑ i, x i`, respectively. This also
 holds when total income is zero, with both coefficients then zero. -/
theorem biasCorrectedGini_eq_mul_gini (x : ι → ℝ) (hn : 2 ≤ Fintype.card ι) :
    biasCorrectedGini x hn = Fintype.card ι / ((Fintype.card ι : ℝ) - 1) * gini x := by
  have hn0 : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast (show Fintype.card ι ≠ 0 by omega)
  unfold biasCorrectedGini gini
  rw [div_mul_div_comm, show ((Fintype.card ι : ℝ) - 1) * (2 * Fintype.card ι * ∑ i, x i) =
    Fintype.card ι * (2 * ((Fintype.card ι : ℝ) - 1) * ∑ i, x i) by ring,
    mul_div_mul_left _ _ hn0]

/-- For a finite population of `n ≥ 2` real incomes `x` and a common factor `t > 0`,
 `biasCorrectedGini (t • x) = biasCorrectedGini x`: both the ordered sum of absolute
 differences and its denominator `2 (n - 1) ∑ i, x i` scale by `t`. Nonnegative incomes
 and positive mean are needed for the income-index interpretation, not for this identity. -/
theorem biasCorrectedGini_smul (x : ι → ℝ) (hn : 2 ≤ Fintype.card ι) {t : ℝ} (ht : 0 < t) :
    biasCorrectedGini (t • x) hn = biasCorrectedGini x hn := by
  rw [biasCorrectedGini_eq_mul_gini, gini_smul x ht, biasCorrectedGini_eq_mul_gini]

/-- Duplicating the two incomes `(0, 1)` to `(0, 0, 1, 1)` changes the bias-corrected Gini
 from `1` to `2/3`. With the ordered-pair normalization `2 (n - 1) ∑ i, x i`, the respective
 numerators are `2` and `8` and denominators `2` and `12`. Thus this normalization fails
 replication invariance even for nonnegative incomes of positive mean. -/
theorem biasCorrectedGini_duplication_example :
    biasCorrectedGini ![0, 1] (by decide) = 1 ∧
      biasCorrectedGini ![0, 0, 1, 1] (by decide) = 2 / 3 := by
  constructor <;> norm_num [biasCorrectedGini, Fin.sum_univ_succ]

end MathlibExt.Economics.Inequality
