/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.TwoMeterReconciliation
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-! # Regression tests for weighted reconciliation of two meters -/

open Matrix MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.GeneralizedLeastSquares

-- A biased first meter shifts the estimate by 4/5 when the variances are 1 and 4.
-- The diagonal working covariance is exact here, so the variance is still 4/5.
example :
    let P := (gaussianReal 1 1).prod (gaussianReal 0 4)
    let E : ℝ × ℝ → ℝ := fun p => (4 * (3 + p.1) + (3 + p.2)) / 5
    (∫ p, E p ∂P) = 19 / 5 ∧ variance E P = 4 / 5 ∧
      (glsMatrix (Matrix.of (fun _ _ => 1) : Matrix (Fin 2) (Fin 1) ℝ)
        (Matrix.diagonal ![1, 4]) *ᵥ ![1, 6]) 0 = 2 ∧
      ((1 - 2) ^ 2 / 1 + (6 - 2) ^ 2 / 4 : ℝ) < (1 - 3) ^ 2 / 1 + (6 - 3) ^ 2 / 4 ∧
      variance E P ≤ variance (fun p : ℝ × ℝ => (3 + p.1) / 2 + (3 + p.2) / 2) P := by
  intro P E
  have h₁ : HasLaw (Prod.fst : ℝ × ℝ → ℝ) (gaussianReal 1 1) P := measurePreserving_fst.hasLaw
  have h₂ : HasLaw (Prod.snd : ℝ × ℝ → ℝ) (gaussianReal 0 4) P := measurePreserving_snd.hasLaw
  have hv₁ : variance (Prod.fst : ℝ × ℝ → ℝ) P = 1 := by
    rw [h₁.variance_eq, variance_id_gaussianReal]
    norm_num
  have hv₂ : variance (Prod.snd : ℝ × ℝ → ℝ) P = 4 := by
    rw [h₂.variance_eq, variance_id_gaussianReal]
    norm_num
  have hcov : covariance (Prod.fst : ℝ × ℝ → ℝ) Prod.snd P = 0 :=
    covariance_fst_snd_prod (memLp_id_gaussianReal 2) (memLp_id_gaussianReal 2)
  have h := two_meter_reconciliation 3 (h₁.memLp (memLp_id_gaussianReal 2))
    (h₂.memLp (memLp_id_gaussianReal 2)) (by norm_num) (by norm_num) hv₁ hv₂
  have hmean := h.2.2.1
  have hvar := (h.2.2.2.1 hcov).1
  have hgls := h.1 1 6
  have hloss := h.2.1 1 6 3 (by norm_num)
  have hopt := (h.2.2.2.1 hcov).2.2 (1 / 2)
  have hA : (fun p : ℝ × ℝ => (1 / 2 : ℝ) * (3 + p.1) + (1 - 1 / 2) * (3 + p.2)) =
      fun p => (3 + p.1) / 2 + (3 + p.2) / 2 := by
    funext p
    ring
  rw [hA] at hopt
  rw [h₁.integral_eq, h₂.integral_eq, integral_id_gaussianReal, integral_id_gaussianReal] at hmean
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num at hmean ⊢
    linarith
  · norm_num [E] at hvar ⊢
    exact hvar
  · norm_num at hgls ⊢
    exact hgls
  · norm_num at hloss ⊢
  · norm_num [E] at hopt ⊢
    exact hopt

-- The second error is twice the first, so its variance is 4 but the errors are correlated.
example : variance (fun z : ℝ => (4 * z + 2 * z) / 5) (gaussianReal 0 1) = 36 / 25 := by
  let P := gaussianReal 0 1
  have hm : MemLp (id : ℝ → ℝ) 2 P := memLp_id_gaussianReal 2
  have hv : variance (id : ℝ → ℝ) P = 1 := by
    rw [variance_id_gaussianReal]
    norm_num
  have hv' : variance (fun z : ℝ => 2 * z) P = 4 := by
    change variance (fun z : ℝ => 2 * id z) P = 4
    rw [variance_const_mul, hv]
    norm_num
  have h := two_meter_reconciliation 0 hm (hm.const_mul 2) (by norm_num) (by norm_num) hv hv'
  have hc := h.2.2.2.2 rfl rfl rfl
  norm_num [P] at hc ⊢
  exact hc
