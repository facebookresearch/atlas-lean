/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecificLimits.DiscountedSum
public import Domains.Economics.Finance.DatedCashFlow

/-! # Present-value bounds for finite cash-flow streams -/

@[expose] public section

namespace MathlibExt.DiscountedSum

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
