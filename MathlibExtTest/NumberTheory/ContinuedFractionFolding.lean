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

/-!
# Tests for `MathlibExt.NumberTheory.ContinuedFractionFolding`

The difference between the proportions of digits `1` and `2` in Cloitre's approximants tends
to `1/3`, and the folding lemma evaluates three concrete folded continued fractions, one of them
with a non-palindromic block at the endpoint `x = 1`.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13 and Theorem 17.
-/

namespace MathlibExtTest.NumberTheory.ContinuedFractionFolding

open MetaMathlibExt

example :
    Filter.Tendsto (fun k =>
      ((cloitreApprox k).count 1 : ℝ) / (cloitreApprox k).length -
        ((cloitreApprox k).count 2 : ℝ) / (cloitreApprox k).length)
      Filter.atTop (nhds (1 / 3)) := by
  obtain ⟨h₁, h₂⟩ := tendsto_cloitreApprox_count_div_length
  convert h₁.sub h₂ using 1
  norm_num

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

-- A non-palindromic block at the endpoint `x = 1`: folding `[0; 1, 2]` reverses the negated
-- block, appending `[1, -2, -1]`, and adds `1 / 9`.
example : finiteContFrac [0, 1, 2, 1, -2, -1] = 7 / 9 := by
  have h := finiteContFrac_add_inv_mul_den_sq 0 [1, 2] (by decide) (by decide) 1
    (by decide)
  have hlist : (0 :: [1, 2]) ++ ((1 : ℕ) : ℤ) ::
      (([1, 2].map (fun b => -b)).reverse) = [0, 1, 2, 1, -2, -1] := by decide
  have hval : finiteContFrac [0, 1, 2] = 2 / 3 := by norm_num [finiteContFrac]
  rw [hlist, hval] at h
  have hden : ((2 / 3 : ℚ)).den = 3 := by
    have heq : (2 / 3 : ℚ) = (((2 : ℤ) / (3 : ℤ) : ℚ)) := by simp
    have hc : ((((2 : ℤ) / (3 : ℤ) : ℚ)).den : ℕ) = 3 := by
      have hcc := Rat.den_div_eq_of_coprime (a := 2) (b := 3) (by decide) (by decide)
      exact_mod_cast hcc
    rw [heq]
    exact hc
  rw [hden] at h
  rw [← h]
  norm_num

end MathlibExtTest.NumberTheory.ContinuedFractionFolding
