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
  myerson_payment_dsic (by intro a b hab; exact le_refl 1)
    (fun a b => by simp [intervalIntegral.integral_const]) v hv b hb

/-- Normalization at a concrete allocation. -/
example : myersonPayment (fun z : ℝ => z) 0 = 0 := myerson_payment_zero
