/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.OmittedVariableBias
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Tests for the sample omitted-variable formula

With `x = (0, 1, 2)`, `z = (0, 1, 1)`, `y = (1, 6, 8)` (exact fit `θ = (1, 2, 3)`):
`S_xx = 2`, `olsSlope x z = 1/2`, `olsSlope x y = 7/2 = 2 + 3 · 1/2`, also via the short fit;
with `z` uncorrelated with `x` the short and long slopes coincide.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.OmittedVariableBias

open MathlibExt.Probability.Causality (popMean)
open MathlibExt.Probability.FiniteProbability
open MathlibExt.Probability.Statistics.OmittedVariableBias
open Finset
open Matrix

/-! Test section: concrete `Fin 3` data with exact values; every hypothesis proved. -/


example : sampleMean (![0, 1, 2] : Fin 3 → ℝ) = 1 := by
  norm_num [sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]

example : sampleMean (![0, 1, 1] : Fin 3 → ℝ) = 2 / 3 := by
  norm_num [sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]

example : sampleMean (![1, 6, 8] : Fin 3 → ℝ) = 5 := by
  norm_num [sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]

example : sxy (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 2] = 2 := by
  norm_num [sxy, sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]

example : sxy (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 1] = 1 := by
  norm_num [sxy, sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]

example : sxy (![0, 1, 2] : Fin 3 → ℝ) ![1, 6, 8] = 7 := by
  norm_num [sxy, sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]

example : olsSlope (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 1] = 1 / 2 := by
  have h1 : sxy (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 1] = 1 := by
    norm_num [sxy, sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]
  have h2 : sxy (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 2] = 2 := by
    norm_num [sxy, sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]
  rw [olsSlope, h1, h2]

example : olsSlope (![0, 1, 2] : Fin 3 → ℝ) ![1, 6, 8] = 7 / 2 := by
  have h1 : sxy (![0, 1, 2] : Fin 3 → ℝ) ![1, 6, 8] = 7 := by
    norm_num [sxy, sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]
  have h2 : sxy (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 2] = 2 := by
    norm_num [sxy, sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]
  rw [olsSlope, h1, h2]

-- The long normal equations for the exact fit `y = 1 + 2x + 3z`.
example : ((longDesignMatrix (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 1])ᵀ
      * longDesignMatrix ![0, 1, 2] ![0, 1, 1]) *ᵥ ![1, 2, 3]
    = (longDesignMatrix ![0, 1, 2] ![0, 1, 1])ᵀ *ᵥ ![1, 6, 8] := by
  have hXθ : longDesignMatrix (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 1] *ᵥ ![1, 2, 3]
      = ![1, 6, 8] := by
    rw [longDesignMatrix_mulVec]
    funext i
    fin_cases i <;> simp <;> norm_num
  rw [← Matrix.mulVec_mulVec, hXθ]

-- Slope form of the omitted-variable formula on the test data.
example : olsSlope (![0, 1, 2] : Fin 3 → ℝ) ![1, 6, 8] = 2 + 3 * (1 / 2) := by
  have hθ : ((longDesignMatrix (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 1])ᵀ
        * longDesignMatrix ![0, 1, 2] ![0, 1, 1]) *ᵥ ![1, 2, 3]
      = (longDesignMatrix ![0, 1, 2] ![0, 1, 1])ᵀ *ᵥ ![1, 6, 8] := by
    have hXθ : longDesignMatrix (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 1] *ᵥ ![1, 2, 3]
        = ![1, 6, 8] := by
      rw [longDesignMatrix_mulVec]
      funext i
      fin_cases i <;> simp <;> norm_num
    rw [← Matrix.mulVec_mulVec, hXθ]
  have hx : sxy (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 2] ≠ 0 := by
    have h2 : sxy (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 2] = 2 := by
      norm_num [sxy, sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]
    rw [h2]
    norm_num
  have hxz : olsSlope (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 1] = 1 / 2 := by
    have h1 : sxy (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 1] = 1 := by
      norm_num [sxy, sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]
    have h2 : sxy (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 2] = 2 := by
      norm_num [sxy, sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]
    rw [olsSlope, h1, h2]
  have e1 : ((![1, 2, 3] : Fin 3 → ℝ)) 1 = 2 := by simp
  have e2 : ((![1, 2, 3] : Fin 3 → ℝ)) 2 = 3 := by simp
  have h := olsSlope_eq_long_add_omitted (θ := ![1, 2, 3]) hθ hx
  rw [e1, e2, hxz] at h
  exact h

-- The short fit `φ = (intercept, slope)` solves the short normal equations.
example : ((designMatrix (![0, 1, 2] : Fin 3 → ℝ))ᵀ * designMatrix ![0, 1, 2]) *ᵥ
      ![olsIntercept ![0, 1, 2] ![1, 6, 8], olsSlope ![0, 1, 2] ![1, 6, 8]]
    = (designMatrix ![0, 1, 2])ᵀ *ᵥ ![1, 6, 8] := by
  have r0 := sum_resid_ols (![0, 1, 2] : Fin 3 → ℝ) ![1, 6, 8]
  have r1 := sum_mul_resid_ols (![0, 1, 2] : Fin 3 → ℝ) ![1, 6, 8]
  rw [← Matrix.mulVec_mulVec, designMatrix_mulVec, transpose_designMatrix_mulVec,
    transpose_designMatrix_mulVec]
  ext j
  fin_cases j
  · simp only [Fin.mk_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h := r0
    rw [Finset.sum_sub_distrib] at h
    linarith
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    have h := r1
    simp only [mul_sub, Finset.sum_sub_distrib] at h
    linarith

-- Short-fit form of the omitted-variable formula on the test data.
example : ((![olsIntercept ![0, 1, 2] ![1, 6, 8],
    olsSlope ![0, 1, 2] ![1, 6, 8]] : Fin 2 → ℝ)) 1 = 2 + 3 * (1 / 2) := by
  have hφ : ((designMatrix (![0, 1, 2] : Fin 3 → ℝ))ᵀ * designMatrix ![0, 1, 2]) *ᵥ
        ![olsIntercept ![0, 1, 2] ![1, 6, 8], olsSlope ![0, 1, 2] ![1, 6, 8]]
      = (designMatrix ![0, 1, 2])ᵀ *ᵥ ![1, 6, 8] := by
    have r0 := sum_resid_ols (![0, 1, 2] : Fin 3 → ℝ) ![1, 6, 8]
    have r1 := sum_mul_resid_ols (![0, 1, 2] : Fin 3 → ℝ) ![1, 6, 8]
    rw [← Matrix.mulVec_mulVec, designMatrix_mulVec, transpose_designMatrix_mulVec,
      transpose_designMatrix_mulVec]
    ext j
    fin_cases j
    · simp only [Fin.mk_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
      have h := r0
      rw [Finset.sum_sub_distrib] at h
      linarith
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      have h := r1
      simp only [mul_sub, Finset.sum_sub_distrib] at h
      linarith
  have hθ : ((longDesignMatrix (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 1])ᵀ
        * longDesignMatrix ![0, 1, 2] ![0, 1, 1]) *ᵥ ![1, 2, 3]
      = (longDesignMatrix ![0, 1, 2] ![0, 1, 1])ᵀ *ᵥ ![1, 6, 8] := by
    have hXθ : longDesignMatrix (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 1] *ᵥ ![1, 2, 3]
        = ![1, 6, 8] := by
      rw [longDesignMatrix_mulVec]
      funext i
      fin_cases i <;> simp <;> norm_num
    rw [← Matrix.mulVec_mulVec, hXθ]
  have hx : sxy (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 2] ≠ 0 := by
    have h2 : sxy (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 2] = 2 := by
      norm_num [sxy, sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]
    rw [h2]
    norm_num
  have hxz : olsSlope (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 1] = 1 / 2 := by
    have h1 : sxy (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 1] = 1 := by
      norm_num [sxy, sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]
    have h2 : sxy (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 2] = 2 := by
      norm_num [sxy, sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]
    rw [olsSlope, h1, h2]
  have e1 : ((![1, 2, 3] : Fin 3 → ℝ)) 1 = 2 := by simp
  have e2 : ((![1, 2, 3] : Fin 3 → ℝ)) 2 = 3 := by simp
  have h := short_eq_long_add_omitted
    (φ := ![olsIntercept ![0, 1, 2] ![1, 6, 8], olsSlope ![0, 1, 2] ![1, 6, 8]])
    (θ := ![1, 2, 3]) hφ hθ hx
  rw [e1, e2, hxz] at h
  exact h

-- Non-vacuity: `z = ![1, 0, 1]` is uncorrelated with `x`.
example : sxy (![0, 1, 2] : Fin 3 → ℝ) ![1, 0, 1] = 0 := by
  norm_num [sxy, sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]

-- Non-vacuity: with uncorrelated `z`, the short slope equals the long slope
-- (`y = 5/2 + (7/2)x - (3/2)z` is an exact fit).
example : olsSlope (![0, 1, 2] : Fin 3 → ℝ) ![1, 6, 8]
    = ((![5 / 2, 7 / 2, -3 / 2] : Fin 3 → ℝ)) 1 := by
  have hθ : ((longDesignMatrix (![0, 1, 2] : Fin 3 → ℝ) ![1, 0, 1])ᵀ
        * longDesignMatrix ![0, 1, 2] ![1, 0, 1]) *ᵥ ![5 / 2, 7 / 2, -3 / 2]
      = (longDesignMatrix ![0, 1, 2] ![1, 0, 1])ᵀ *ᵥ ![1, 6, 8] := by
    have hXθ : longDesignMatrix (![0, 1, 2] : Fin 3 → ℝ) ![1, 0, 1] *ᵥ
          ![5 / 2, 7 / 2, -3 / 2] = ![1, 6, 8] := by
      rw [longDesignMatrix_mulVec]
      funext i
      fin_cases i <;> simp <;> norm_num
    rw [← Matrix.mulVec_mulVec, hXθ]
  have hx : sxy (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 2] ≠ 0 := by
    have h2 : sxy (![0, 1, 2] : Fin 3 → ℝ) ![0, 1, 2] = 2 := by
      norm_num [sxy, sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]
    rw [h2]
    norm_num
  have hz : sxy (![0, 1, 2] : Fin 3 → ℝ) ![1, 0, 1] = 0 := by
    norm_num [sxy, sampleMean, popMean, Fin.sum_univ_three, Fintype.card_fin]
  have h0 : olsSlope (![0, 1, 2] : Fin 3 → ℝ) ![1, 0, 1] = 0 := by
    rw [olsSlope, hz, zero_div]
  have h := olsSlope_eq_long_add_omitted (θ := ![5 / 2, 7 / 2, -3 / 2]) hθ hx
  rw [h0] at h
  rw [h]
  ring

end MathlibExtTest.Probability.Statistics.OmittedVariableBias
