/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ContinuedFractionFolding
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.NumberTheory.ContinuedFractionFolding` -/

namespace MathlibExtTest.NumberTheory.ContinuedFractionFolding

open MetaMathlibExt

-- Folding `[1; 2, 2]` by `x = 3` appends `[3, -2, -2]` and adds `1 / 75`.
example : finiteContFrac [1, 2, 2, 3, -2, -2] = 106 / 75 := by
  have h := finiteContFrac_add_inv_mul_den_sq 1 [2, 2] (by decide) (by decide) 3
    (by decide)
  have hlist : (1 :: [2, 2]) ++ ((3 : ℕ) : ℤ) ::
      (([2, 2].map (fun b => -b)).reverse) = [1, 2, 2, 3, -2, -2] := by decide
  rw [hlist, finiteContFrac_one_two_two] at h
  have hden : ((7 / 5 : ℚ)).den = 5 := by
    have heq : (7 / 5 : ℚ) = (((7 : ℤ) / (5 : ℤ) : ℚ)) := by simp
    have hc : ((((7 : ℤ) / (5 : ℤ) : ℚ)).den : ℕ) = 5 := by
      have hcc := Rat.den_div_eq_of_coprime (a := 7) (b := 5) (by decide) (by decide)
      exact_mod_cast hcc
    rw [heq]
    exact hc
  rw [hden] at h
  rw [← h]
  norm_num

-- Folding `[-1; 1, 1]` by `x = 2` appends `[2, -1, -1]` and adds `1 / 8`.
example : finiteContFrac [-1, 1, 1, 2, -1, -1] = -3 / 8 := by
  have h := finiteContFrac_add_inv_mul_den_sq (-1) [1, 1] (by decide) (by decide) 2
    (by decide)
  have hlist : (-1 :: [1, 1]) ++ ((2 : ℕ) : ℤ) ::
      (([1, 1].map (fun b => -b)).reverse) = [-1, 1, 1, 2, -1, -1] := by decide
  have hval : finiteContFrac [-1, 1, 1] = -1 / 2 := by norm_num [finiteContFrac]
  rw [hlist, hval] at h
  have hden : ((-1 / 2 : ℚ)).den = 2 := by
    have heq : (-1 / 2 : ℚ) = (((-1 : ℤ) / (2 : ℤ) : ℚ)) := by simp
    have hc : ((((-1 : ℤ) / (2 : ℤ) : ℚ)).den : ℕ) = 2 := by
      have hcc := Rat.den_div_eq_of_coprime (a := -1) (b := 2) (by decide) (by decide)
      exact_mod_cast hcc
    rw [heq]
    exact hc
  rw [hden] at h
  rw [← h]
  norm_num

end MathlibExtTest.NumberTheory.ContinuedFractionFolding
