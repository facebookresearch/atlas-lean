/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.Measurement.GaussianLatentMean
import Mathlib.Tactic.NormNum

/-! # Regression tests for latent Gaussian mean nonidentification -/

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.Measurement

-- The slope is negative and has magnitude two: variance multiplies by four, not by two.
example :
    let P := (gaussianReal 2 1).prod (gaussianReal 0 1)
    let F' : ℝ × ℝ → ℝ := fun p => 5 + (-2) * p.1
    let X' : ℝ × ℝ → ℝ := fun p => 9 + (-1) * F' p + p.2
    HasLaw F' (gaussianReal 1 4) P ∧ IndepFun F' Prod.snd P ∧
      X' = (fun p => 4 + 2 * p.1 + p.2) ∧ HasLaw X' (gaussianReal 8 5) P := by
  intro P F' X'
  have hF : HasLaw (Prod.fst : ℝ × ℝ → ℝ) (gaussianReal 2 1) P := measurePreserving_fst.hasLaw
  have hε : HasLaw (Prod.snd : ℝ × ℝ → ℝ) (gaussianReal 0 1) P := measurePreserving_snd.hasLaw
  have hind : IndepFun (Prod.fst : ℝ × ℝ → ℝ) Prod.snd P :=
    indepFun_prod measurable_id measurable_id
  have h := gaussian_latent_affine_invariance hF hε hind 4 2 5 (b := -2) (by norm_num)
  have hFour (h : 0 ≤ (4 : ℝ)) : NNReal.mk 4 h = 4 := by
    apply NNReal.eq
    norm_num [NNReal.coe_mk]
  have hFive : (4 : NNReal) + 1 = 5 := by norm_num
  norm_num [F', X'] at h ⊢
  simpa only [hFour, hFive] using h

-- The second group's latent factor has mean -1 in model B but its indicator has mean 1.
example :
    ((gaussianReal (-1) 1).prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ => 2 + p.1 + p.2) =
      gaussianReal 1 2 := by
  have h := (gaussian_latent_mean_nonidentification.1 (1 : Fin 2)).2
  norm_num at h ⊢
  exact h
