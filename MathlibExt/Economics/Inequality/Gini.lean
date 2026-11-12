/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# Scale invariance of the Gini coefficient

The finite Gini coefficient of incomes `x` over a population of size `n` is the mean absolute
difference over twice the mean, `(∑ i, ∑ j, |x i - x j|) / (2 n ∑ i, x i)`. It is the usual
Gini index when total income is positive.

Multiplying every income by the same positive factor leaves it unchanged (`gini_smul`). The
identity needs no positivity of total income (with total `0` both sides are `0`), but it does
need a positive factor: a negative factor flips the sign.

## Main results

* `MathlibExt.Economics.Inequality.gini_smul`

Atlas roadmap target AP05.T01.
-/

namespace MathlibExt.Economics.Inequality

open Finset

/-- Finite Gini coefficient of the income distribution `x` over the population `ι`:
mean absolute difference over twice the mean,
`(∑ i, ∑ j, |x i - x j|) / (2 * n * ∑ i, x i)` with `n = card ι`. It is the usual Gini
index when total income is positive; when the total is `0` the division yields `0`. -/
noncomputable def gini {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  (∑ i, ∑ j, |x i - x j|) / (2 * Fintype.card ι * ∑ i, x i)

/-- **Scale invariance of the Gini coefficient.** Multiplying every income by the same positive
factor `t` leaves the Gini coefficient unchanged. (The identity needs no positivity of total
income; positivity of `t` is necessary, since `t = -1` flips the sign.) -/
theorem gini_smul {ι : Type*} [Fintype ι] (x : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    gini (t • x) = gini x := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have habs : ∀ a b : ℝ, |t * a - t * b| = t * |a - b| := fun a b => by
    rw [← mul_sub, abs_mul, abs_of_pos ht]
  have hpt : ∀ i : ι, (t • x) i = t * x i := fun i => by
    rw [Pi.smul_apply, smul_eq_mul]
  have hnum : (∑ i, ∑ j, |(t • x) i - (t • x) j|) = t * ∑ i, ∑ j, |x i - x j| := by
    have h1 : ∀ i : ι, (∑ j, |(t • x) i - (t • x) j|) = t * ∑ j, |x i - x j| :=
      fun i => by simp_rw [hpt, habs, ← Finset.mul_sum]
    simp_rw [h1, ← Finset.mul_sum]
  have hden : (∑ i, (t • x) i) = t * ∑ i, x i := by simp_rw [hpt, ← Finset.mul_sum]
  unfold gini
  rw [hnum, hden]
  have hring : (2 : ℝ) * Fintype.card ι * (t * ∑ i, x i)
      = t * (2 * Fintype.card ι * ∑ i, x i) := by ring
  rw [hring, mul_div_mul_left _ _ ht0]

/-- **Scale invariance of the Gini coefficient, source form.** For an income distribution with
positive total income, scaling every income by the same positive factor `t` leaves the Gini
coefficient unchanged. This is `gini_smul` restricted to the domain where `gini` is the usual
Gini index. -/
theorem gini_smul_of_sum_pos {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : 0 < ∑ i, x i) {t : ℝ}
    (ht : 0 < t) : gini (t • x) = gini x := by
  exact gini_smul x ht

end MathlibExt.Economics.Inequality
