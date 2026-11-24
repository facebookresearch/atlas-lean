/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.CoprimeDenominatorProgressions

open MetaMathlibExt

-- At the smallest allowed denominator, even an integer step leaves both starts nonintegral.
example (i j : ℕ) :
    (1 / 3 : ℝ) + i * 2 ∉ Set.range ((↑) : ℕ → ℝ) ∧
      2 * (1 / 3 : ℝ) + j * 2 ∉ Set.range ((↑) : ℕ → ℝ) :=
  add_mul_not_mem_nat_of_coprime_den _ _ 0 2 1 0 3 1
    (by decide) (by decide) (by decide) (by simp) (by simp) i j

-- Doubling 1/4 cancels a factor of two. The step fraction 3/9 need not be reduced.
example (j : ℕ) :
    2 * (1 / 4 : ℝ) + j * (3 / 9 : ℝ) ∉ Set.range ((↑) : ℕ → ℝ) :=
  (add_mul_not_mem_nat_of_coprime_den _ _ 0 0 1 3 4 9
    (by decide) (by decide) (by decide) (by simp) (by simp) 0 j).2

-- The two ends of the denominator window cannot both give natural-number points.
example (x : ℝ) (h₁ : x + ((1 : ℕ) : ℝ) * (2 + 1 / 3 : ℝ) ∈ Set.range ((↑) : ℕ → ℝ)) :
    x + ((2 : ℕ) : ℝ) * (2 + 1 / 3 : ℝ) ∉ Set.range ((↑) : ℕ → ℝ) := by
  intro h₂
  have h := eq_of_add_mul_rat_mem_nat x (2 + 1 / 3) 2 1 3
    (by decide) (by decide) (by decide) (by simp) 2 1
    (by decide) (by decide) (by decide) (by decide) h₂ h₁
  exact (by decide : (2 : ℕ) ≠ 1) h
