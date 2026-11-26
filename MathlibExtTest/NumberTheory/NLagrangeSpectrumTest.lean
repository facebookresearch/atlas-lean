/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.NLagrangeSpectrum

-- At `k = 1` for `ξ = √2`, the convergent is `1`, the complete quotient is
-- `√2 + 1`, the reversed prefix is empty, and the identity of
-- `MetaMathlibExt.convergent_quality_and_lagrange_limsup` reads
-- `-1 / (1 - √2) = √2 + 1`.
example : (-1 : ℝ) ^ 1 / (((Real.sqrt 2).convergent 0).den ^ 2 *
    (((Real.sqrt 2).convergent 0 : ℝ) - Real.sqrt 2)) = Real.sqrt 2 + 1 := by
  have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have h := (MetaMathlibExt.convergent_quality_and_lagrange_limsup _ hirr).1 1 (by norm_num)
  have h1lt : (1 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have h2lt : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hfloor : ⌊Real.sqrt 2⌋ = 1 := by
    rw [Int.floor_eq_iff]
    refine ⟨by exact_mod_cast h1lt.le, by norm_num [Real.sqrt_lt']⟩
  have hconv : (Real.sqrt 2).convergent 0 = 1 := by
    rw [Real.convergent_zero, hfloor]
    norm_cast
  rw [hconv] at h
  dsimp only at h
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hfract : Int.fract (Real.sqrt 2) = Real.sqrt 2 - 1 := by
    rw [← Int.self_sub_floor, hfloor]
    norm_num
  have hcq1 : (fun x : ℝ => (Int.fract x)⁻¹)^[1] (Real.sqrt 2) = Real.sqrt 2 + 1 := by
    simp only [Function.iterate_one]
    rw [hfract]
    exact inv_eq_of_mul_eq_one_left (by nlinarith [hsq])
  rw [hconv]
  simp only [Rat.den_one, Rat.cast_one] at h
  simp only [Rat.den_one, Rat.cast_one]
  rw [hcq1] at h
  simp at h
  rw [hfloor, hfract] at h
  linear_combination h
