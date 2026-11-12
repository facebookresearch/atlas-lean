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
