/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import MathlibExt.NumberTheory.GoldenRatioLeftFactorialLambertKurepaPartialIntegralLambertSequenceBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.Real.GoldenRatio
import MathlibExt.NumberTheory.GoldenFactorialExponent
import MathlibExt.NumberTheory.GoldenRatioLambertSequence

namespace MathlibExtTest.NumberTheory.GoldenRatioLeftFactorialLambertKurepaPartialIntegralLambertSequenceBounds

open MetaMathlibExt

example : ∃ a : ℝ, ((((5 : ℕ))) : ℝ) - 1 ≤ a
    ∧ lambertMap (-a / ((((5 : ℕ)) : ℝ) - 1))
      = -(1 / ((((5 : ℕ)) : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((((5 : ℕ)) : ℝ) - 1))
    ∧ ⌊kurepaPartialIntegral 5 a⌋ = 33 := by
  have hr0 : (0 : ℝ) < (4 / 7 : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : (4 / 7 : ℝ) ^ ((1 : ℝ) / 4) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num)
  have he3 : (1 / 3 : ℝ) < Real.exp (-1) := by
    rw [Real.exp_neg, one_div]
    exact (inv_lt_inv₀ (by norm_num) (Real.exp_pos _)).mpr Real.exp_one_lt_three
  have he : (1 / 4 : ℝ) < Real.exp (-1) := by linarith [he3]
  have h14 : (1 / 4 : ℝ) * (4 / 7 : ℝ) ^ ((1 : ℝ) / 4) ≤ 1 / 4 := by
    have h := mul_le_mul_of_nonneg_left hr1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    simpa using h
  have hx1 : -Real.exp (-1) ≤ -(1 / 4) * (4 / 7 : ℝ) ^ ((1 : ℝ) / 4) := by
    linarith [he, h14]
  have hx0 : -(1 / 4) * (4 / 7 : ℝ) ^ ((1 : ℝ) / 4) < 0 :=
    mul_neg_of_neg_of_pos (by norm_num) hr0
  obtain ⟨⟨y, hy⟩, hxy⟩ :=
    (existsUnique_lambertMap_lower_preimage (x := -(1 / 4) * (4 / 7 : ℝ) ^ ((1 : ℝ) / 4))
      hx1 hx0).exists
  have ha4 : (4 : ℝ) ≤ -4 * y := by linarith [show y ≤ -1 from hy]
  have hW4 : lambertMap (-(-4 * y) / 4) = -(1 / 4) * (4 / 7 : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [show -(-4 * y) / 4 = y by ring]
    exact hxy
  have hd4 : ((((5 : ℕ))) : ℝ) - 1 = 4 := by norm_num
  have ha : ((((5 : ℕ))) : ℝ) - 1 ≤ -4 * y := by rw [hd4]; exact ha4
  have hW : lambertMap (-(-4 * y) / ((((5 : ℕ)) : ℝ) - 1))
      = -(1 / ((((5 : ℕ)) : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((((5 : ℕ)) : ℝ) - 1)) := by
    rw [hd4]
    exact hW4
  have hmain := kurepaPartialIntegral_lambertSequence_bounds 5 (by norm_num) (-4 * y) ha hW
  have hSn : (∑ k ∈ Finset.range 5, k.factorial) = 34 := by decide
  have hS : (∑ k ∈ Finset.range 5, ((k.factorial : ℕ) : ℝ)) = 34 := by
    rw [← Nat.cast_sum, hSn]
    norm_num
  obtain ⟨hlo, hhi⟩ := hmain
  have hKlo : (33 : ℝ) < kurepaPartialIntegral 5 (-4 * y) := by linarith [hlo, hhi, hS]
  have hKhi : kurepaPartialIntegral 5 (-4 * y) < 34 := by linarith [hlo, hhi, hS]
  have hfloor : ⌊kurepaPartialIntegral 5 (-4 * y)⌋ = 33 := by
    rw [Int.floor_eq_iff]
    constructor
    · exact_mod_cast hKlo.le
    · have h : kurepaPartialIntegral 5 (-4 * y) < 33 + 1 := by linarith [hKhi]
      exact_mod_cast h
  exact ⟨-4 * y, ha, hW, hfloor⟩

example : ∃ a : ℝ, ((((9 : ℕ))) : ℝ) - 1 ≤ a
    ∧ lambertMap (-a / ((((9 : ℕ)) : ℝ) - 1))
      = -(1 / ((((9 : ℕ)) : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((((9 : ℕ)) : ℝ) - 1))
    ∧ ⌊kurepaPartialIntegral 9 a⌋ = 46233 := by
  have hr0 : (0 : ℝ) < (4 / 7 : ℝ) ^ ((1 : ℝ) / 8) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : (4 / 7 : ℝ) ^ ((1 : ℝ) / 8) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num)
  have he3 : (1 / 3 : ℝ) < Real.exp (-1) := by
    rw [Real.exp_neg, one_div]
    exact (inv_lt_inv₀ (by norm_num) (Real.exp_pos _)).mpr Real.exp_one_lt_three
  have he : (1 / 8 : ℝ) < Real.exp (-1) := by linarith [he3]
  have h18 : (1 / 8 : ℝ) * (4 / 7 : ℝ) ^ ((1 : ℝ) / 8) ≤ 1 / 8 := by
    have h := mul_le_mul_of_nonneg_left hr1 (by norm_num : (0 : ℝ) ≤ 1 / 8)
    simpa using h
  have hx1 : -Real.exp (-1) ≤ -(1 / 8) * (4 / 7 : ℝ) ^ ((1 : ℝ) / 8) := by
    linarith [he, h18]
  have hx0 : -(1 / 8) * (4 / 7 : ℝ) ^ ((1 : ℝ) / 8) < 0 :=
    mul_neg_of_neg_of_pos (by norm_num) hr0
  obtain ⟨⟨y, hy⟩, hxy⟩ :=
    (existsUnique_lambertMap_lower_preimage (x := -(1 / 8) * (4 / 7 : ℝ) ^ ((1 : ℝ) / 8))
      hx1 hx0).exists
  have ha8 : (8 : ℝ) ≤ -8 * y := by linarith [show y ≤ -1 from hy]
  have hW8 : lambertMap (-(-8 * y) / 8) = -(1 / 8) * (4 / 7 : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [show -(-8 * y) / 8 = y by ring]
    exact hxy
  have hd8 : ((((9 : ℕ))) : ℝ) - 1 = 8 := by norm_num
  have ha : ((((9 : ℕ))) : ℝ) - 1 ≤ -8 * y := by rw [hd8]; exact ha8
  have hW : lambertMap (-(-8 * y) / ((((9 : ℕ)) : ℝ) - 1))
      = -(1 / ((((9 : ℕ)) : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((((9 : ℕ)) : ℝ) - 1)) := by
    rw [hd8]
    exact hW8
  have hmain := kurepaPartialIntegral_lambertSequence_bounds 9 (by norm_num) (-8 * y) ha hW
  have hSn : (∑ k ∈ Finset.range 9, k.factorial) = 46234 := by decide
  have hS : (∑ k ∈ Finset.range 9, ((k.factorial : ℕ) : ℝ)) = 46234 := by
    rw [← Nat.cast_sum, hSn]
    norm_num
  obtain ⟨hlo, hhi⟩ := hmain
  have hKlo : (46233 : ℝ) < kurepaPartialIntegral 9 (-8 * y) := by linarith [hlo, hhi, hS]
  have hKhi : kurepaPartialIntegral 9 (-8 * y) < 46234 := by linarith [hlo, hhi, hS]
  have hfloor : ⌊kurepaPartialIntegral 9 (-8 * y)⌋ = 46233 := by
    rw [Int.floor_eq_iff]
    constructor
    · exact_mod_cast hKlo.le
    · have h : kurepaPartialIntegral 9 (-8 * y) < 46233 + 1 := by linarith [hKhi]
      exact_mod_cast h
  exact ⟨-8 * y, ha, hW, hfloor⟩

end MathlibExtTest.NumberTheory.GoldenRatioLeftFactorialLambertKurepaPartialIntegralLambertSequenceBounds
