/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Log.GaudronRemondConstants

open Real

-- The constant of Lemme 8.4 for `ε = 1/8`.
example : 6 * 16 ^ 2 / ((1 - 1 / 8) * π) * (136 + 68 * log (2 * π ^ 2 / (1 / 8))) ≤ exp 12.5 :=
  GaudronRemond.eightPeriods_constant_le_exp

-- The three estimates of p. 2097 at `b = 1` and `b = 2`.
example : GaudronRemond.c₂ 1 ≤ 287 := by
  simpa using GaudronRemond.c₂_le 1 le_rfl

example : 1600 * 287 * exp 12.5 * (4 * 1 : ℝ) ^ 12 * (1 : ℝ) ^ 9 ≤ 2 ^ 64 := by
  simpa using GaudronRemond.key_le_two_pow 1 le_rfl

example : GaudronRemond.c₁ 2 * GaudronRemond.c₂ 2 ≤ 16 ^ 256 := by
  have := GaudronRemond.c₁_mul_c₂_le 2 (by norm_num)
  norm_num at this ⊢
  exact this

-- The exponent computation with `t = 1` and `g = n₁ = g₁ = d₁ = 1`, `ν = ν₁ = 0`, `P = 2`:
-- `(10)^5 L^4 L₁^8 ≤ 9^96 2^1024` whenever `L ≤ 2^(-116) 9^8` and `L₁ ≤ 9^4`.
example (L L₁ : ℝ) (hL : 0 < L) (hL₁ : 0 < L₁) (hLb : L ≤ 2 ^ (-116 : ℤ) * 9 ^ 8)
    (hL₁b : L₁ ≤ 9 ^ 4) :
    (10 : ℝ) ^ 5 * L ^ 4 * L₁ ^ 8 ≤ 9 ^ 96 * 2 ^ 1024 := by
  have := GaudronRemond.isogeny_bound_exponents (t := 1) 1 le_rfl (fun _ ↦ 1) (fun _ ↦ 1)
    (fun _ ↦ 1) (by simp) 0 (fun _ ↦ 0) (by norm_num) (fun _ ↦ by norm_num)
    (fun _ ↦ by norm_num) 2 L (fun _ ↦ L₁) (by norm_num) hL (fun _ ↦ hL₁)
    (by simpa using hLb) (fun _ ↦ by simpa using hL₁b)
  norm_num at this ⊢
  exact this
