/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecificLimits.DiscountedSum
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Discounted geometric sums

A constant cash flow `c` received at each date `t = 0, 1, 2, …` and discounted by the factor
`q ^ t` has the discounted geometric sum `∑' t, q ^ t * c`, the discounted value
`MathlibExt.DiscountedSum.discountedValue q (fun _ => c)` of the constant stream. When the
absolute ratio `|q|` is below one, the series converges with sum `c / (1 - q)`.

The ratio may be negative. `MathlibExt.DiscountedSum.summable_discounted` requires
`0 ≤ q < 1`, and Mathlib's `hasSum_geometric_of_abs_lt_one` is the unscaled series `∑ q ^ t`
with sum `(1 - q)⁻¹`; the results below scale it by the cash flow `c`.

## Main results

* `MathlibExt.DiscountedSum.hasSum_discountedGeometricSum`: for `|q| < 1`, the discounted
  cash flows `q ^ t * c` have sum `c / (1 - q)`.
* `MathlibExt.DiscountedSum.tendsto_sum_range_discountedGeometricSum`: for `|q| < 1`, the
  partial sums `∑ t ∈ Finset.range n, q ^ t * c` converge to `c / (1 - q)`.
* `MathlibExt.DiscountedSum.discountedGeometricSum_eq`: for `|q| < 1`,
  `discountedGeometricSum q c = c / (1 - q)`.

## References

* J. Stewart, *Calculus: Early Transcendentals*, 8th ed., Cengage Learning (2015),
  Section 11.2 (geometric series).

Atlas roadmap target M02.T03.
-/

@[expose] public section

namespace MathlibExt.DiscountedSum

/-- The discounted geometric sum `∑' t, q ^ t * c` of the constant cash flow `c` at the ratio
`q`, over the dates `t = 0, 1, 2, …`: the discounted value of the constant stream
`fun _ => c`. It equals `c / (1 - q)` when `|q| < 1` (`discountedGeometricSum_eq`); when the
series is not summable, Lean's `tsum` is `0`. -/
noncomputable def discountedGeometricSum (q c : ℝ) : ℝ :=
  discountedValue q (fun _ => c)

/-- **Convergence of the discounted geometric sum.** For `|q| < 1`, the discounted constant
cash flows `q ^ t * c` are summable with sum `c / (1 - q)`. -/
theorem hasSum_discountedGeometricSum {q : ℝ} (hq : |q| < 1) (c : ℝ) :
    HasSum (fun t : ℕ => q ^ t * c) (c / (1 - q)) := by
  rw [div_eq_mul_inv c (1 - q), mul_comm c ((1 - q)⁻¹)]
  exact (hasSum_geometric_of_abs_lt_one hq).mul_right c

/-- For `|q| < 1`, the partial sums `∑ t ∈ Finset.range n, q ^ t * c` of the discounted
geometric sum converge to `c / (1 - q)` as `n → ∞`. -/
theorem tendsto_sum_range_discountedGeometricSum {q : ℝ} (hq : |q| < 1) (c : ℝ) :
    Filter.Tendsto (fun n : ℕ => ∑ t ∈ Finset.range n, q ^ t * c) Filter.atTop
      (nhds (c / (1 - q))) := by
  exact (hasSum_discountedGeometricSum hq c).tendsto_sum_nat

/-- **Closed form.** For `|q| < 1`, the discounted geometric sum of the constant cash flow `c`
at ratio `q` is `c / (1 - q)`. -/
theorem discountedGeometricSum_eq {q : ℝ} (hq : |q| < 1) (c : ℝ) :
    discountedGeometricSum q c = c / (1 - q) := by
  unfold discountedGeometricSum discountedValue
  exact (hasSum_discountedGeometricSum hq c).tsum_eq

end MathlibExt.DiscountedSum
