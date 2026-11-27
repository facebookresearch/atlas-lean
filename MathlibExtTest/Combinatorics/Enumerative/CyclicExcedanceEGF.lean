/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CyclicExcedanceEGF

open MetaMathlibExt PowerSeries

-- The empty term vanishes and the singleton term is independent of the weight.
example (x : ℚ) (hx : x ≠ 1) :
    coeff 0 (X + logOf (C (x - 1) * (C x * exp ℚ - rescale x (exp ℚ))⁻¹)) = 0 ∧
      coeff 1 (X + logOf (C (x - 1) * (C x * exp ℚ - rescale x (exp ℚ))⁻¹)) = 1 := by
  rw [← cyclicExcedanceEGF_eq x hx]
  have h₀ : circularEulerian 1 0 = 1 := circularEulerian_small.2.1
  have h₁ : circularEulerian 1 1 = 0 := by decide
  simp [Finset.sum_range_succ, h₀, h₁]

-- The transposition has one excedance.
example (x : ℚ) (hx : x ≠ 1) :
    coeff 2 (X + logOf (C (x - 1) * (C x * exp ℚ - rescale x (exp ℚ))⁻¹)) = x / 2 := by
  rw [← cyclicExcedanceEGF_eq x hx]
  have h₀ : circularEulerian 2 0 = 0 := by decide
  have h₁ : circularEulerian 2 1 = 1 := by decide
  have h₂ : circularEulerian 2 2 = 0 := by decide
  norm_num [Finset.sum_range_succ, h₀, h₁, h₂, Nat.factorial]

-- The two three-cycles have different excedance counts, and cancel at weight minus one.
example :
    coeff 3 (X + logOf (C (-2 : ℚ) *
      (C (-1 : ℚ) * exp ℚ - rescale (-1) (exp ℚ))⁻¹)) = 0 := by
  rw [show (-2 : ℚ) = -1 - 1 by norm_num, ← cyclicExcedanceEGF_eq (-1) (by norm_num)]
  have h₀ : circularEulerian 3 0 = 0 := by decide
  have h₃ : circularEulerian 3 3 = 0 := by decide
  norm_num [Finset.sum_range_succ, h₀, circularEulerian_small.2.2.1,
    circularEulerian_small.2.2.2, h₃]
