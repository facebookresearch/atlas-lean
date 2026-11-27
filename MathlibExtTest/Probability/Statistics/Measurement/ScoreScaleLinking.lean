/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.Measurement.ScoreScaleLinking
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.NormNum

/-! # Regression tests for linear linking of score scales -/

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.Measurement

-- The inverse laws need only real scale parameters, not a probability model.
example :
    let link := fun x : ℝ => 7 + (5 / 2) * (x - 3)
    let unlink := fun y : ℝ => 3 + (2 / 5) * (y - 7)
    unlink (link (-1)) = -1 ∧ link (unlink 12) = 12 := by
  have h := linear_score_scale_linking.{0} 3 7 (σX := 2) (σY := 5) (by norm_num) (by norm_num)
  exact ⟨h.1 (-1), h.2.1 12⟩

-- Link a source with mean 3 and SD 2 to a target with mean 7 and SD 5.
example :
    let P := gaussianReal 3 4
    let link := fun x : ℝ => 7 + (5 / 2) * (x - 3)
    (∫ x, link x ∂P) = 7 ∧ populationSD P link = 5 := by
  intro P link
  have hmean : (∫ x : ℝ, id x ∂P) = 3 := integral_id_gaussianReal
  have hsd : populationSD P id = 2 := by
    have hv : variance (id : ℝ → ℝ) P = (2 : ℝ) ^ 2 := by
      dsimp only [P]
      rw [variance_id_gaussianReal]
      norm_num
    unfold populationSD
    rw [hv, Real.sqrt_sq (by norm_num)]
  exact (linear_score_scale_linking 3 7 (σX := 2) (σY := 5)
    (by norm_num) (by norm_num)).2.2 P id (memLp_id_gaussianReal 2) hmean hsd
