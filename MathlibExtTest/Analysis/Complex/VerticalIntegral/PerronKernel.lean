/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.VerticalIntegral.PerronKernel

/-!
# Tests for the Perron-type kernels on a vertical line

Concrete values of the discontinuous integral (as a limit of PNT+'s truncations `VIntegral'`)
and of the higher-order and factorial kernels (also as PNT+ line integrals `VerticalIntegral'`),
and consistency of the `x ≥ 1` and `x ≤ 1` formulas at the common point `x = 1`.
-/

@[expose] public section

open Complex
open scoped Real

/-! ### The discontinuous integral -/

example : HasVerticalIntegral 1 (fun s : ℂ => ((2 : ℝ) : ℂ) ^ s / s) 1 :=
  hasVerticalIntegral_cpow_div_self_of_one_lt (by norm_num) (by norm_num)

example : HasVerticalIntegral 2 (fun s : ℂ => ((1 / 2 : ℝ) : ℂ) ^ s / s) 0 :=
  hasVerticalIntegral_cpow_div_self_of_lt_one (by norm_num) (by norm_num) (by norm_num)

/-- **The principal value of `1 / s`** on `re s = 1` is `1 / 2`. -/
example : HasVerticalIntegral 1 (fun s : ℂ => 1 / s) (1 / 2) :=
  hasVerticalIntegral_one_div one_pos

/-- `1 / s` is not integrable on the line, so its value is a limit of PNT+'s truncated
integrals `VIntegral'`. -/
example : Filter.Tendsto (fun R : ℝ => VIntegral' (fun s : ℂ => 1 / s) (1 / 3) (-R) R)
    Filter.atTop (nhds (1 / 2)) :=
  (hasVerticalIntegral_one_div (by norm_num)).tendsto_vIntegral'

/-- At `x = 1` the integrand `1 ^ s / s` is `1 / s`, so the value is `1 / 2`, strictly between
the values `0` and `1` on either side. -/
example : HasVerticalIntegral 1 (fun s : ℂ => ((1 : ℝ) : ℂ) ^ s / s) (1 / 2) :=
  (hasVerticalIntegral_one_div one_pos).congr_line fun t => by simp

/-- The value depends on `x`: it is not `1` at `x = 1`. -/
example : ¬ HasVerticalIntegral 1 (fun s : ℂ => 1 / s) 1 := fun h => by
  have := (hasVerticalIntegral_one_div one_pos).unique h
  norm_num at this

/-! ### The higher-order kernel -/

/-- `(1 / 2πi) ∫ e ^ s / s² ds = log e = 1`. -/
example : HasVerticalIntegral 1 (fun s : ℂ => ((Real.exp 1 : ℝ) : ℂ) ^ s / s ^ (1 + 1)) 1 := by
  have h := hasVerticalIntegral_cpow_div_pow_succ_of_one_le (k := 1) le_rfl one_pos
    (Real.one_le_exp zero_le_one)
  simpa using h

/-- The same value as a PNT+ line integral: the integrand is integrable for `k ≥ 1`. -/
example : VerticalIntegral' (fun s : ℂ => ((Real.exp 1 : ℝ) : ℂ) ^ s / s ^ (2 + 1)) 1 = 1 / 2 := by
  rw [verticalIntegral'_cpow_div_pow_succ_of_one_le (by norm_num) one_pos
    (Real.one_le_exp zero_le_one)]
  simp [Nat.factorial]

example : VerticalIntegral' (fun s : ℂ => ((1 / 2 : ℝ) : ℂ) ^ s / s ^ (1 + 1)) 3 = 0 :=
  verticalIntegral'_cpow_div_pow_succ_of_le_one le_rfl (by norm_num) (by norm_num) (by norm_num)

/-- At `x = 1` the two formulas agree: `(log 1) ^ k / k! = 0`. -/
example (k : ℕ) (hk : 1 ≤ k) :
    (Real.log 1 : ℂ) ^ k / (k.factorial : ℂ) = 0 :=
  (hasVerticalIntegral_cpow_div_pow_succ_of_one_le hk one_pos le_rfl).unique
    (hasVerticalIntegral_cpow_div_pow_succ_of_le_one hk one_pos one_pos le_rfl)

example : HasVerticalIntegral 1 (fun s : ℂ => ((1 / 2 : ℝ) : ℂ) ^ s / s ^ (3 + 1)) 0 :=
  hasVerticalIntegral_cpow_div_pow_succ_of_le_one (by norm_num) one_pos (by norm_num)
    (by norm_num)

/-! ### The Riesz (factorial) kernel -/

/-- `k = 1`, `x = 2`: `(1 / 2πi) ∫ 2 ^ s / (s (s + 1)) ds = 1 - 1 / 2 = 1 / 2`. -/
example : HasVerticalIntegral 1
    (fun s : ℂ => ((2 : ℝ) : ℂ) ^ s / ∏ j ∈ Finset.range (1 + 1), (s + j)) (1 / 2) := by
  have h := hasVerticalIntegral_cpow_div_prod_of_one_le (k := 1) le_rfl one_pos
    (by norm_num : (1 : ℝ) ≤ 2)
  convert h using 1
  norm_num

/-- The same value as a PNT+ line integral. -/
example : VerticalIntegral'
    (fun s : ℂ => ((2 : ℝ) : ℂ) ^ s / ∏ j ∈ Finset.range (1 + 1), (s + j)) 1 = 1 / 2 := by
  rw [verticalIntegral'_cpow_div_prod_of_one_le le_rfl one_pos (by norm_num)]
  norm_num

example : VerticalIntegral'
    (fun s : ℂ => ((1 / 2 : ℝ) : ℂ) ^ s / ∏ j ∈ Finset.range (2 + 1), (s + j)) 1 = 0 :=
  verticalIntegral'_cpow_div_prod_of_le_one (by norm_num) one_pos (by norm_num) (by norm_num)

/-- At `x = 1` the two formulas agree: `(1 - 1 / 1) ^ k / k! = 0`. -/
example (k : ℕ) (hk : 1 ≤ k) : (1 - 1 / ((1 : ℝ) : ℂ)) ^ k / (k.factorial : ℂ) = 0 :=
  (hasVerticalIntegral_cpow_div_prod_of_one_le hk one_pos le_rfl).unique
    (hasVerticalIntegral_cpow_div_prod_of_le_one hk one_pos zero_le_one le_rfl)

/-- `x = 0` is allowed for the factorial kernel: `0 ^ s = 0` on the line. -/
example : HasVerticalIntegral 1
    (fun s : ℂ => ((0 : ℝ) : ℂ) ^ s / ∏ j ∈ Finset.range (2 + 1), (s + j)) 0 :=
  hasVerticalIntegral_cpow_div_prod_of_le_one (by norm_num) one_pos le_rfl zero_le_one
