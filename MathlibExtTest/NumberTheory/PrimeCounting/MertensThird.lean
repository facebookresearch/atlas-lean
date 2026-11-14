/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.MertensThird

/-!
# Tests for Mertens' third theorem
-/

@[expose] public section

open Filter

example : Tendsto (fun x : ℝ => (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)) * Real.log x)
    atTop (nhds (Real.exp (-Real.eulerMascheroniConstant))) :=
  Nat.tendsto_prod_primesLE_one_sub_inv_mul_log

-- Consequence: the Mertens product is eventually positive times `log x`, and tends to `0`.
example : Tendsto (fun x : ℝ => ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)) atTop (nhds 0) := by
  have h := Nat.tendsto_prod_primesLE_one_sub_inv_mul_log.mul
    (Real.tendsto_log_atTop.inv_tendsto_atTop)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  simp [Pi.inv_apply, this]

example : Tendsto (fun x : ℝ => (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹) / Real.log x)
    atTop (nhds (Real.exp Real.eulerMascheroniConstant)) :=
  Nat.tendsto_prod_primesLE_inv_one_sub_inv_div_log
