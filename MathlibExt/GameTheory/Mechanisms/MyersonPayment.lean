/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Data.Real.Basic

@[expose] public section

/-! # Myerson's payment identity

For a monotone allocation rule `x`, the payment
`p z = z * x z - ∫₀ᶻ x` makes truthful bidding dominant (DSIC), and
it is normalized: `p 0 = 0`. Together with the monotonicity direction
in `MathlibExt/GameTheory/Mechanisms/Myerson.lean` this is roadmap
package DPA-46 of the Atlas TCS canon roadmap.

Source: R. Myerson, "Optimal auction design", Mathematics of
Operations Research 6 (1981), 58--73.
-/

open MeasureTheory intervalIntegral

/-- The Myerson payment for a monotone allocation rule `x` in a
single-parameter auction, for a bidder whose own bid is `z` (other
bids suppressed from the notation): the payment identity
`p z = z * x z - ∫₀ᶻ x`. -/
noncomputable def myersonPayment (x : ℝ → ℝ) (z : ℝ) : ℝ :=
  z * x z - ∫ t in (0:ℝ)..z, x t

/-- DSIC of the Myerson payment: if the allocation `x` is monotone
nondecreasing and integrable on compact intervals, then a bidder
with nonnegative valuation `v` maximizes `v * x b - myersonPayment x b`
over reports `b ≥ 0` at the truthful report `b = v`. -/
theorem myerson_payment_dsic {x : ℝ → ℝ} (hmono : Monotone x)
    (hint : ∀ a b : ℝ, IntervalIntegrable x MeasureTheory.volume a b)
    (v : ℝ) (hv : 0 ≤ v) (b : ℝ) (hb : 0 ≤ b) :
    v * x b - myersonPayment x b ≤ v * x v - myersonPayment x v := by
  unfold myersonPayment
  rcases le_total b v with h | h
  · have h_add := intervalIntegral.integral_add_adjacent_intervals (hint 0 b) (hint b v)
    have h_le : ∀ t ∈ Set.Icc b v, x b ≤ x t := fun t ht => hmono (Set.mem_Icc.mp ht).1
    have h_int : (∫ t in b..v, x b) ≤ ∫ t in b..v, x t :=
      intervalIntegral.integral_mono_on h intervalIntegrable_const (hint b v) h_le
    rw [intervalIntegral.integral_const] at h_int
    rw [smul_eq_mul] at h_int
    have heq1 : v * x b - (b * x b - ∫ t in (0:ℝ)..b, x t)
        = (v - b) * x b + ∫ t in (0:ℝ)..b, x t := by ring
    have heq2 : v * x v - (v * x v - ∫ t in (0:ℝ)..v, x t)
        = ∫ t in (0:ℝ)..v, x t := by ring
    rw [heq1, heq2]
    linarith
  · have h_add := intervalIntegral.integral_add_adjacent_intervals (hint 0 v) (hint v b)
    have h_le : ∀ t ∈ Set.Icc v b, x t ≤ x b := fun t ht => hmono (Set.mem_Icc.mp ht).2
    have h_int : (∫ t in v..b, x t) ≤ ∫ t in v..b, x b :=
      intervalIntegral.integral_mono_on h (hint v b) intervalIntegrable_const h_le
    rw [intervalIntegral.integral_const] at h_int
    rw [smul_eq_mul] at h_int
    have heq1 : v * x b - (b * x b - ∫ t in (0:ℝ)..b, x t)
        = (v - b) * x b + ∫ t in (0:ℝ)..b, x t := by ring
    have heq2 : v * x v - (v * x v - ∫ t in (0:ℝ)..v, x t)
        = ∫ t in (0:ℝ)..v, x t := by ring
    rw [heq1, heq2]
    linarith

/-- The Myerson payment is normalized: a bid of `0` pays `0`. -/
theorem myerson_payment_zero {x : ℝ → ℝ} : myersonPayment x 0 = 0 := by
  unfold myersonPayment
  rw [intervalIntegral.integral_same]
  ring
