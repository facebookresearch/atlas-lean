/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LogisticRegression

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.LogisticRegression

open MathlibExt.Probability.Statistics.LogisticRegression

/-- Concrete test: with a single observation, unit design, and `y = 0`,
the NLL at `β = 0` is `log 2`. -/
example : logisticNLL (fun _ _ => (1 : ℝ)) (![0] : Fin 1 → ℝ)
    (![0] : Fin 1 → ℝ) = Real.log 2 := by
  simp [logisticNLL]
  norm_num [Real.exp_zero]

/-- Concrete test of the outcome term: one observation with design `2`,
outcome `y = 1`, and coefficient `β = 3`, so `x ⬝ β = 6` and the NLL is
`log (1 + exp 6) - 6`. A different sign or coefficient on the
`- yᵢ (xᵢ ⬝ β)` term would change this value. -/
example : logisticNLL (fun _ _ => (2 : ℝ)) (![1] : Fin 1 → ℝ)
    (![3] : Fin 1 → ℝ) = Real.log (1 + Real.exp 6) - 6 := by
  simp [logisticNLL]
  norm_num

/-- Concrete test: the one-dimensional softplus `β ↦ log (1 + exp β)`
is convex, as the specialization of `convexOn_logisticNLL` to a single
observation with unit design and `y = 0`. -/
example : ConvexOn ℝ Set.univ
    (fun β : Fin 1 → ℝ => Real.log (1 + Real.exp (β 0))) := by
  have h := convexOn_logisticNLL (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℝ))
    (![0] : Fin 1 → ℝ)
  have hfun : logisticNLL (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℝ)) (![0] : Fin 1 → ℝ)
      = (fun β : Fin 1 → ℝ => Real.log (1 + Real.exp (β 0))) := by
    funext β
    simp [logisticNLL]
  rw [hfun] at h
  exact h


end MathlibExtTest.Probability.Statistics.LogisticRegression
