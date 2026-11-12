/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.Mechanisms.MyersonPayment

/-- Direct evaluation of the payment definition at a constant allocation:
`myersonPayment (fun _ => 1) z = z * 1 - ∫₀ᶻ 1 = z - z = 0`. -/
example (z : ℝ) : myersonPayment (fun _ : ℝ => (1 : ℝ)) z = 0 := by
  unfold myersonPayment
  rw [intervalIntegral.integral_const]
  simp

/-- Constant allocation `x = 1`: the utility `v * 1 - myersonPayment x b`
is `v` at every report `b`, so truthfulness is an equality case. -/
example (v b : ℝ) :
    v * (fun _ : ℝ => (1 : ℝ)) b - myersonPayment (fun _ : ℝ => (1 : ℝ)) b = v := by
  unfold myersonPayment
  rw [intervalIntegral.integral_const]
  simp

/-- Constant allocation `x = 1`: the Myerson payment at bid `z` is
`z - z = 0`, and truthfulness is an equality case; check the DSIC
statement instantiates. -/
example (v b : ℝ) (hv : 0 ≤ v) (hb : 0 ≤ b) :
    v * (fun _ : ℝ => (1 : ℝ)) b - myersonPayment (fun _ : ℝ => (1 : ℝ)) b ≤
      v * (fun _ : ℝ => (1 : ℝ)) v - myersonPayment (fun _ : ℝ => (1 : ℝ)) v :=
  myerson_payment_dsic (by intro a ha b hb hab; exact le_refl 1) v hv b hb

/-- Normalization at a concrete allocation. -/
example : myersonPayment (fun z : ℝ => z) 0 = 0 := myerson_payment_zero

/-- Identity allocation on admissible reports, with unrelated negative values. -/
private noncomputable def nonnegativeAllocation (z : ℝ) : ℝ :=
  if 0 ≤ z then z else 1

private theorem nonnegativeAllocation_monotone :
    MonotoneOn nonnegativeAllocation (Set.Ici 0) := by
  intro a ha b hb hab
  simpa [nonnegativeAllocation, Set.mem_Ici.mp ha, Set.mem_Ici.mp hb] using hab

/-- The witness fails the old global monotonicity requirement. -/
example : ¬ Monotone nonnegativeAllocation := by
  intro h
  have hle := h (a := -1) (b := 0) (by norm_num)
  norm_num [nonnegativeAllocation] at hle

/-- Truthfulness needs only monotonicity on admissible reports. -/
example (v b : ℝ) (hv : 0 ≤ v) (hb : 0 ≤ b) :
    v * nonnegativeAllocation b - myersonPayment nonnegativeAllocation b ≤
      v * nonnegativeAllocation v - myersonPayment nonnegativeAllocation v :=
  myerson_payment_dsic nonnegativeAllocation_monotone v hv b hb

/-- Underreporting at the zero boundary. -/
example :
    2 * nonnegativeAllocation 0 - myersonPayment nonnegativeAllocation 0 ≤
      2 * nonnegativeAllocation 2 - myersonPayment nonnegativeAllocation 2 :=
  myerson_payment_dsic nonnegativeAllocation_monotone 2 (by norm_num)
    0 (by norm_num)

/-- Overreporting with zero valuation. -/
example :
    0 * nonnegativeAllocation 2 - myersonPayment nonnegativeAllocation 2 ≤
      0 * nonnegativeAllocation 0 - myersonPayment nonnegativeAllocation 0 :=
  myerson_payment_dsic nonnegativeAllocation_monotone 0 (by norm_num)
    2 (by norm_num)
