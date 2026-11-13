/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import MathlibExt.Economics.Finance.DatedCashFlow

/-!
# Truncation error of discounted sums

For a discount factor `0 ≤ β < 1` and rewards with `|r t| ≤ M`, the discounted value
`∑' t, β ^ t * r t` exists and its `T`-period truncation is within `M * β ^ T / (1 - β)` of it.

## i. Overview

The tail after `T` periods is split off with `Summable.sum_add_tsum_nat_add` and dominated by the
geometric series `M * β ^ T * ∑ β ^ t` (`tsum_of_norm_bounded`, `hasSum_geometric_of_lt_one`).
The bound is attained by constant rewards. The truncation is the present value of the first `T`
rewards under the discount factors `t ↦ β ^ t` in the sense of
`MathlibExt.Economics.Finance.presentValue`, so the bound also applies to present values.

## ii. Main results

* `MathlibExt.DiscountedSum.summable_discounted`
* `MathlibExt.DiscountedSum.abs_discountedValue_sub_truncatedValue_le`
* `MathlibExt.DiscountedSum.truncatedValue_eq_presentValue`
* `MathlibExt.DiscountedSum.abs_discountedValue_sub_presentValue_le`

## iii. References

* M. L. Puterman, *Markov Decision Processes*, §6.2.
-/

@[expose] public section

namespace MathlibExt.DiscountedSum

/-- The infinite-horizon discounted value `∑' t, β ^ t * r t` of the reward stream `r`
at discount factor `β`. It is meaningful when the series is summable
(`summable_discounted`); otherwise Lean's `tsum` is `0`. -/
noncomputable def discountedValue (β : ℝ) (r : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * r t

/-- The `T`-period truncation `∑ t ∈ range T, β ^ t * r t` of the discounted value. -/
noncomputable def truncatedValue (β : ℝ) (r : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, β ^ t * r t

/-- A bounded reward stream has a summable discounted series when `0 ≤ β < 1`. -/
theorem summable_discounted {β M : ℝ} {r : ℕ → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hr : ∀ t, |r t| ≤ M) : Summable fun t => β ^ t * r t := by
  have hgeo : Summable fun n => β ^ n := summable_geometric_of_lt_one hβ0 hβ1
  have hM : Summable fun n => M * β ^ n := hgeo.mul_left M
  refine Summable.of_norm_bounded hM (fun t => ?_)
  show ‖β ^ t * r t‖ ≤ M * β ^ t
  have hnn : 0 ≤ β ^ t := pow_nonneg hβ0 t
  have h1 : ‖β ^ t * r t‖ = β ^ t * |r t| := by
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
  rw [h1, mul_comm (β ^ t) _]
  exact mul_le_mul_of_nonneg_right (hr t) hnn

/-- **Truncation error bound.** For `0 ≤ β < 1` and `|r t| ≤ M` for all `t`, the error of the
`T`-period truncation is at most `M * β ^ T / (1 - β)`. -/
theorem abs_discountedValue_sub_truncatedValue_le {β M : ℝ} {r : ℕ → ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hr : ∀ t, |r t| ≤ M) (T : ℕ) :
    |discountedValue β r - truncatedValue β r T| ≤ M * β ^ T / (1 - β) := by
  have hsum : Summable fun t => β ^ t * r t := summable_discounted hβ0 hβ1 hr
  have hsplit : (∑ i ∈ Finset.range T, β ^ i * r i) + (∑' i, β ^ (i + T) * r (i + T))
      = ∑' i, β ^ i * r i :=
    Summable.sum_add_tsum_nat_add T hsum
  have hdiff : discountedValue β r - truncatedValue β r T
      = ∑' i, β ^ (i + T) * r (i + T) := by
    unfold discountedValue truncatedValue
    linarith
  rw [hdiff, ← Real.norm_eq_abs]
  have hgeo : HasSum (fun n => β ^ n) (1 - β)⁻¹ := hasSum_geometric_of_lt_one hβ0 hβ1
  have hmul : HasSum (fun i => (M * β ^ T) * β ^ i) ((M * β ^ T) * (1 - β)⁻¹) :=
    HasSum.mul_left (M * β ^ T) hgeo
  have hbound : ‖∑' i, β ^ (i + T) * r (i + T)‖ ≤ (M * β ^ T) * (1 - β)⁻¹ := by
    refine tsum_of_norm_bounded hmul (fun i => ?_)
    show ‖β ^ (i + T) * r (i + T)‖ ≤ (M * β ^ T) * β ^ i
    have hnn : 0 ≤ β ^ (i + T) := pow_nonneg hβ0 _
    have h1 : ‖β ^ (i + T) * r (i + T)‖ = β ^ (i + T) * |r (i + T)| := by
      simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
    rw [h1, pow_add]
    calc β ^ i * β ^ T * |r (i + T)|
        = |r (i + T)| * (β ^ i * β ^ T) := by ring
      _ ≤ M * (β ^ i * β ^ T) :=
          mul_le_mul_of_nonneg_right (hr _) (mul_nonneg (pow_nonneg hβ0 _) (pow_nonneg hβ0 _))
      _ = (M * β ^ T) * β ^ i := by ring
  rw [div_eq_mul_inv]
  exact hbound

/-- The truncation is the present value of the first `T` rewards under the discount factors
`t ↦ β ^ t` (`MathlibExt.Economics.Finance.presentValue`). -/
theorem truncatedValue_eq_presentValue (β : ℝ) (r : ℕ → ℝ) (T : ℕ) :
    truncatedValue β r T =
      MathlibExt.Economics.Finance.presentValue (fun t => β ^ t) (Finset.range T) r := by
  rfl

/-- **Truncation error bound, present-value form.** For `0 ≤ β < 1` and `|r t| ≤ M`, the present
value of the first `T` rewards is within `M * β ^ T / (1 - β)` of the discounted value. -/
theorem abs_discountedValue_sub_presentValue_le {β M : ℝ} {r : ℕ → ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hr : ∀ t, |r t| ≤ M) (T : ℕ) :
    |discountedValue β r -
        MathlibExt.Economics.Finance.presentValue (fun t => β ^ t) (Finset.range T) r| ≤
      M * β ^ T / (1 - β) := by
  rw [← truncatedValue_eq_presentValue]
  exact abs_discountedValue_sub_truncatedValue_le hβ0 hβ1 hr T

end MathlibExt.DiscountedSum
