/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.ExpSumZeros

/-!
# Tests for zeros of real exponential sums

A two-term instance, the empty sum, and a boundary probe showing that `|S| - 1` points do not
suffice.
-/

@[expose] public section

open Finset

namespace MathlibExtTest.Analysis.SpecialFunctions.ExpSumZeros

/-- Two rates `0, 1` and two points `1, 2`: `c₀ + c₁ e^{-a}` vanishing at `a = 1, 2` forces
`c₀ = c₁ = 0`. -/
example (c : ℝ → ℝ) (h1 : c 0 + c 1 * Real.exp (-1) = 0)
    (h2 : c 0 + c 1 * Real.exp (-2) = 0) : c 0 = 0 ∧ c 1 = 0 := by
  have h := Real.eq_zero_of_sum_mul_exp_eq_zero (S := {0, 1}) (P := {1, 2})
    (by rw [card_pair zero_ne_one, card_pair (by norm_num)]) c
    (fun a ha => by
      rcases mem_insert.1 ha with rfl | ha
      · rw [sum_pair zero_ne_one]; simpa using h1
      · rw [mem_singleton.1 ha, sum_pair zero_ne_one]; simpa using h2)
  exact ⟨h 0 (by simp), h 1 (by simp)⟩

/-- The empty sum: there is nothing to prove. -/
example (c : ℝ → ℝ) : ∀ u ∈ (∅ : Finset ℝ), c u = 0 :=
  Real.eq_zero_of_sum_mul_exp_eq_zero (P := ∅) le_rfl c (by simp)

/-- Boundary: one point is not enough for two rates; `1 - e · e^{-a}` vanishes at `a = 1`
with nonzero coefficients. -/
example : ∑ u ∈ ({0, 1} : Finset ℝ), (if u = 0 then 1 else -Real.exp 1) *
    Real.exp (-(1 * u)) = 0 := by
  rw [sum_pair zero_ne_one]
  simp only [↓reduceIte, mul_zero, neg_zero, Real.exp_zero, mul_one, one_ne_zero]
  rw [neg_mul, ← Real.exp_add]
  simp

end MathlibExtTest.Analysis.SpecialFunctions.ExpSumZeros
