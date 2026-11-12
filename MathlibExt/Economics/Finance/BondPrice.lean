/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.DatedCashFlow
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Bond price as discounted coupon and redemption cash flows

A bond pays coupon `c` at each date `t = 1, …, n` and redeems face `F` at
maturity `n`. Its price at per-period rate `r` is the FI01 present value of
those cash flows.

## Main results

* `MathlibExt.Economics.Finance.bondPrice_eq_coupon_plus_redemption`: the price
  splits into the coupon stream plus the discounted face value
  (`Finset.sum_add_distrib`, `Finset.sum_eq_single`).

## References

SOA Exam FM syllabus (bonds); OpenStax, *Principles of Finance*, time value of
money. Atlas roadmap target FI03.T01.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance

/-- Cash flow of a bond at date `t`: coupon `coupon` at every payment date, plus face
`face` at maturity `n` (source clause: "coupon at each date, redemption at maturity"). -/
noncomputable def bondCashFlow (coupon face : ℝ) (n : ℕ) (t : ℕ) : ℝ :=
  coupon + (if t = n then face else 0)

/-- Price of the bond at per-period rate `r`: the FI01 present value of its cash
flows over the payment dates `1, …, n` (source clause: "price = PV of coupons
plus redemption"). -/
noncomputable def bondPrice (coupon face : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  presentValue (discountFactor r) (Finset.Icc 1 n) (bondCashFlow coupon face n)

/-- Bond price splits into the coupon stream plus the discounted face value
(Atlas roadmap FI03.T01). Requires `1 ≤ n` so that maturity lies in the
payment dates; no sign hypothesis on coupon, face, or rate is needed. -/
theorem bondPrice_eq_coupon_plus_redemption (coupon face : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (r : ℝ) :
    bondPrice coupon face n r =
      coupon * (∑ t ∈ Finset.Icc 1 n, discountFactor r t) +
        discountFactor r n * face := by
  unfold bondPrice presentValue bondCashFlow
  simp only [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.sum_mul]
    exact mul_comm _ _
  · have hmem : n ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hn, le_rfl⟩
    have h0 : ∀ t ∈ Finset.Icc 1 n, t ≠ n →
        discountFactor r t * (if t = n then face else 0) = 0 := by
      intro t _ htne
      simp [htne]
    have h1 : n ∉ Finset.Icc 1 n →
        discountFactor r n * (if n = n then face else 0) = 0 := by
      intro hcontra
      exact absurd hmem hcontra
    rw [Finset.sum_eq_single n h0 h1]
    simp

end MathlibExt.Economics.Finance
