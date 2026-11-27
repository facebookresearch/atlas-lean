/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.TranscendentalDilateSumsetAIMCombinatoricsProblem264
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Tests for `MathlibExt.Combinatorics.TranscendentalDilateSumsetAIMCombinatoricsProblem264` -/

namespace MathlibExtTest.TranscendentalDilateSumsetAIMCombinatoricsProblem264

open MathlibExt.Combinatorics.TranscendentalDilateSumsetAIMCombinatoricsProblem264Wanted
open scoped Pointwise

-- Test section: edge cases of the statement. For the empty set both sides are `0`, with the
-- convention `log 0 = 0`.
example (α c : ℝ) :
    Real.exp (c * Real.sqrt (Real.log (∅ : Finset ℝ).card)) * (∅ : Finset ℝ).card =
      (((∅ : Finset ℝ) + α • ∅).card : ℝ) := by
  simp

-- A singleton is an equality case for every constant: both sides are `1`.
example (α a c : ℝ) :
    Real.exp (c * Real.sqrt (Real.log ({a} : Finset ℝ).card)) * ({a} : Finset ℝ).card =
      ((({a} : Finset ℝ) + α • {a}).card : ℝ) := by
  simp

-- Test section: consequences of the theorem. Adding a transcendental dilate never shrinks a set.
example (α : ℝ) (hα : Transcendental ℚ α) (A : Finset ℝ) : A.card ≤ (A + α • A).card := by
  obtain ⟨c, hc, h⟩ := transcendentalDilateLowerBound_holds
  have h1 := h α hα A
  have h2 : 1 ≤ Real.exp (c * Real.sqrt (Real.log A.card)) :=
    Real.one_le_exp (mul_nonneg hc.le (Real.sqrt_nonneg _))
  have h3 : (A.card : ℝ) ≤ (A + α • A).card := by
    nlinarith [Nat.cast_nonneg (α := ℝ) A.card]
  exact_mod_cast h3

-- The bound is not vacuous: the ratio `|A + α • A| / |A|` exceeds every constant `K` once `|A|` is
-- large, uniformly in the transcendental number `α`.
example (K : ℝ) : ∃ N : ℕ, ∀ α : ℝ, Transcendental ℚ α → ∀ A : Finset ℝ, N ≤ A.card →
    K * A.card ≤ (A + α • A).card := by
  obtain ⟨c, hc, h⟩ := transcendentalDilateLowerBound_holds
  refine ⟨⌈Real.exp ((Real.log K / c) ^ 2)⌉₊ + 1, fun α hα A hA => ?_⟩
  have h1 := h α hα A
  have hK : K ≤ Real.exp (c * Real.sqrt (Real.log A.card)) := by
    rcases le_or_gt K 0 with hK0 | hK0
    · exact hK0.trans (Real.exp_pos _).le
    · have hN : Real.exp ((Real.log K / c) ^ 2) ≤ A.card := by
        have h2 := Nat.le_ceil (Real.exp ((Real.log K / c) ^ 2))
        have h3 : (⌈Real.exp ((Real.log K / c) ^ 2)⌉₊ : ℝ) + 1 ≤ A.card := by
          exact_mod_cast hA
        linarith
      have hpos : (0 : ℝ) < A.card := lt_of_lt_of_le (Real.exp_pos _) hN
      have hlog : (Real.log K / c) ^ 2 ≤ Real.log A.card := by
        rw [← Real.exp_le_exp, Real.exp_log hpos]
        exact hN
      have hsq : Real.log K / c ≤ Real.sqrt (Real.log A.card) :=
        calc Real.log K / c ≤ |Real.log K / c| := le_abs_self _
          _ = Real.sqrt ((Real.log K / c) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ Real.sqrt (Real.log A.card) := Real.sqrt_le_sqrt hlog
      calc K = Real.exp (Real.log K) := (Real.exp_log hK0).symm
        _ ≤ Real.exp (c * Real.sqrt (Real.log A.card)) := by
          apply Real.exp_le_exp.mpr
          have h4 := mul_le_mul_of_nonneg_left hsq hc.le
          rwa [mul_div_cancel₀ _ hc.ne'] at h4
  calc K * A.card ≤ Real.exp (c * Real.sqrt (Real.log A.card)) * A.card := by gcongr
    _ ≤ _ := h1

end MathlibExtTest.TranscendentalDilateSumsetAIMCombinatoricsProblem264
