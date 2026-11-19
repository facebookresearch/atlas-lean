/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.AmericanCall
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Finance.AmericanCall

open MathlibExt.Economics.Finance.BinomialOptimalStopping

example : (1/3 : ℝ) * 2 + (1 - 1/3) * (1/2) = 1 := by norm_num

example : snell (1/3) 1⁻¹ (callPayoff 4 2 (1/2) 4) 1 [] = 4/3 := by
  show snell (1/3 : ℝ) (1:ℝ)⁻¹ (callPayoff 4 2 (1/2) 4) (0 + 1) [] = 4/3
  simp [snell, continuation, callPayoff, stockPrice]
  norm_num

example : ruleValue (1/3) 1⁻¹ (callPayoff 4 2 (1/2) 4) europeanRule 1 [] = 4/3 := by
  show ruleValue (1/3 : ℝ) (1:ℝ)⁻¹ (callPayoff 4 2 (1/2) 4) europeanRule (0 + 1) [] = 4/3
  simp [ruleValue, europeanRule, continuation, callPayoff, stockPrice]
  norm_num

example : snell (1/3 : ℝ) (1:ℝ)⁻¹ (callPayoff 4 2 (1/2) 4) 1 [] =
    ruleValue (1/3) (1:ℝ)⁻¹ (callPayoff 4 2 (1/2) 4) europeanRule 1 [] :=
  snell_call_eq_european (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1
    []

example : (1/7 : ℝ) * 2 + (1 - 1/7) * (1/4) = 1/2 := by norm_num

example : snell (1/7) (1/2)⁻¹ (callPayoff 4 2 (1/4) 1) 1 [] = 3 := by
  show snell (1/7 : ℝ) ((1/2 : ℝ))⁻¹ (callPayoff 4 2 (1/4) 1) (0 + 1) [] = 3
  simp [snell, continuation, callPayoff, stockPrice]
  norm_num

example : ruleValue (1/7) (1/2)⁻¹ (callPayoff 4 2 (1/4) 1) europeanRule 1 [] = 2 := by
  show ruleValue (1/7 : ℝ) ((1/2 : ℝ))⁻¹ (callPayoff 4 2 (1/4) 1) europeanRule (0 + 1) [] = 2
  simp [ruleValue, europeanRule, continuation, callPayoff, stockPrice]
  norm_num

example : snell (1/7 : ℝ) ((1/2 : ℝ))⁻¹ (callPayoff 4 2 (1/4) 1) 1 [] ≠
    ruleValue (1/7) ((1/2 : ℝ))⁻¹ (callPayoff 4 2 (1/4) 1) europeanRule 1 [] := by
  have h1 : snell (1/7 : ℝ) ((1/2 : ℝ))⁻¹ (callPayoff 4 2 (1/4) 1) 1 [] = 3 := by
    show snell (1/7 : ℝ) ((1/2 : ℝ))⁻¹ (callPayoff 4 2 (1/4) 1) (0 + 1) [] = 3
    simp [snell, continuation, callPayoff, stockPrice]
    norm_num
  have h2 : ruleValue (1/7 : ℝ) ((1/2 : ℝ))⁻¹ (callPayoff 4 2 (1/4) 1) europeanRule 1 [] = 2 := by
    show ruleValue (1/7 : ℝ) ((1/2 : ℝ))⁻¹ (callPayoff 4 2 (1/4) 1) europeanRule (0 + 1) [] = 2
    simp [ruleValue, europeanRule, continuation, callPayoff, stockPrice]
    norm_num
  rw [h1, h2]
  norm_num

end MathlibExtTest.Economics.Finance.AmericanCall
