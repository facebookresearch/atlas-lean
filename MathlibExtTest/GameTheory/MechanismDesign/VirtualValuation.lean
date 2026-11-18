/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.MechanismDesign.VirtualValuation
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

open Set MathlibExt.GameTheory.MechanismDesign.SingleParameter

/-! Myerson's example (1981, §5): one bidder with value uniform on `[0, 100]`. -/

/-- The virtual valuation of the uniform distribution on `[0, 100]` is `2 t - 100`. -/
theorem virtualValue_uniform (t : ℝ) :
    virtualValue (fun _ => (1 / 100 : ℝ)) 0 t = 2 * t - 100 := by
  simp only [virtualValue, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  field_simp
  ring

theorem uniform_one : ∫ _ in (0 : ℝ)..100, (1 / 100 : ℝ) = 1 := by
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  norm_num

/-- The posted price `50` earns `25`. -/
example : ∫ t in (0 : ℝ)..100, postedPricePayment 50 t * (1 / 100) = 25 := by
  rw [integral_postedPricePayment_mul_density (a := 0) (b := 100) ⟨by norm_num, by norm_num⟩
    continuousOn_const uniform_one]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  norm_num

/-- No incentive-compatible, individually rational mechanism earns more than the posted price
`50` from this bidder (Myerson's optimal reserve price). -/
example {Q P : ℝ → ℝ} (h : IsIncentiveCompatibleOn Q P 0 100)
    (hQ : ∀ t ∈ Icc (0 : ℝ) 100, Q t ∈ Icc (0 : ℝ) 1) (hU : 0 ≤ truthfulUtility Q P 0) :
    ∫ t in (0 : ℝ)..100, P t * (1 / 100) ≤
      ∫ t in (0 : ℝ)..100, postedPricePayment 50 t * (1 / 100) := by
  refine integral_payment_mul_density_le_postedPrice (by norm_num) continuousOn_const
    (fun _ _ => by norm_num) uniform_one ⟨by norm_num, by norm_num⟩ ?_ ?_ h hQ hU
  · intro t _ ht
    rw [virtualValue_uniform]; linarith
  · intro t _ ht
    rw [virtualValue_uniform]; linarith

/-- The revenue identity on a concrete incentive-compatible mechanism: the posted price `50`. -/
example : ∫ t in (0 : ℝ)..100, postedPricePayment 50 t * (1 / 100) =
    (∫ t in (0 : ℝ)..100,
      virtualValue (fun _ => (1 / 100 : ℝ)) 0 t * postedPriceAlloc 50 t * (1 / 100)) -
      truthfulUtility (postedPriceAlloc 50) (postedPricePayment 50) 0 :=
  integral_payment_mul_density (by norm_num) continuousOn_const (fun _ _ => by norm_num)
    uniform_one (isIncentiveCompatibleOn_postedPrice 50 0 100)
