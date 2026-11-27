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

/-- The summed NLL is the negative canonical GLM log-likelihood on a
one-observation example with a nonzero outcome term. -/
example :
    logisticNLL (fun _ _ => (2 : ℝ)) (![1] : Fin 1 → ℝ)
        (![3] : Fin 1 → ℝ) =
      -MathlibExt.Probability.Statistics.GLM.logisticLogLik
        (fun _ _ => (2 : ℝ)) 0 (![1] : Fin 1 → ℝ) (![3] : Fin 1 → ℝ) :=
  logisticNLL_eq_neg_logisticLogLik _ _ _

/-- Positive gradient check from the contract: one observation, unit design,
and outcome `0` give Euclidean gradient `σ(θ)`. -/
example (θ : ℝ) :
    gradient
        (fun b : EuclideanSpace ℝ (Fin 1) =>
          logisticNLL (fun _ _ => (1 : ℝ)) (![0] : Fin 1 → ℝ) b.ofLp)
        (WithLp.toLp 2 ![θ]) =
      WithLp.toLp 2 ![Real.sigmoid θ] := by
  have h := gradient_logisticNLL (fun _ _ => (1 : ℝ)) (![0] : Fin 1 → ℝ)
    (WithLp.toLp 2 ![θ])
  rw [h]
  congr 1
  ext j
  fin_cases j
  simp [MathlibExt.Probability.Statistics.GLM.glmPredictor, Matrix.mulVec,
    Matrix.transpose, dotProduct]

/-- Zero-design boundary: the gradient and objective gap vanish without
dividing by the zero smoothness constant. -/
example (β βstar : EuclideanSpace ℝ (Fin 2)) :
    gradient
        (fun b : EuclideanSpace ℝ (Fin 2) =>
          logisticNLL (0 : Matrix (Fin 2) (Fin 2) ℝ) ![0, 1] b.ofLp) β = 0 ∧
      logisticNLL (0 : Matrix (Fin 2) (Fin 2) ℝ) ![0, 1] β.ofLp -
          logisticNLL (0 : Matrix (Fin 2) (Fin 2) ℝ) ![0, 1] βstar.ofLp = 0 :=
  ⟨gradient_logisticNLL_of_X_eq_zero rfl _ β,
    logisticNLL_gap_eq_zero_of_X_eq_zero rfl _ β βstar⟩

/-- Complete separation has no finite unregularized minimizer, using the
canonical GLM separation design. -/
example :
    ¬ ∃ β, IsMinOn
      (logisticNLL
        MathlibExt.Probability.Statistics.GLM.separationDesign ![0, 1])
      Set.univ β :=
  not_exists_isMinOn_of_separable _ _
    (by intro i; fin_cases i <;> simp)
    (βsep := ![1])
    (by
      intro i
      fin_cases i <;>
        simp [MathlibExt.Probability.Statistics.GLM.separationDesign,
          Matrix.mulVec, dotProduct])

/-- API shape check for the gradient-descent adapter. -/
example {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ)
    {βstar : EuclideanSpace ℝ (Fin m)}
    (hmin : ∀ b : EuclideanSpace ℝ (Fin m),
      logisticNLL X y βstar.ofLp ≤ logisticNLL X y b.ofLp)
    {η : ℝ}
    (hL : 0 < ‖(Matrix.toEuclideanLin X).toContinuousLinearMap‖ ^ 2 / 4)
    (hη : η ∈ Set.Ioc 0
      (1 / (‖(Matrix.toEuclideanLin X).toContinuousLinearMap‖ ^ 2 / 4)))
    {βseq : ℕ → EuclideanSpace ℝ (Fin m)}
    (hβseq : ∀ k, βseq (k + 1) = βseq k -
      η • gradient (fun b : EuclideanSpace ℝ (Fin m) => logisticNLL X y b.ofLp)
        (βseq k)) (k : ℕ) (hk : 0 < k) :
    logisticNLL X y (βseq k).ofLp - logisticNLL X y βstar.ofLp ≤
      ‖βseq 0 - βstar‖ ^ 2 / (2 * η * (k : ℝ)) :=
  gd_logisticNLL_rate X y hmin hL hη hβseq k hk


-- Different signed margins for the two labels; the same ray drives both losses to zero.
example : sInf (Set.range (logisticNLL (![![-2], ![3]] : Matrix (Fin 2) (Fin 1) ℝ)
      (![0, 1] : Fin 2 → ℝ))) = 0 :=
  (logisticNLL_infimum_zero_not_attained_of_separable _ _
    (by intro i; fin_cases i <;> simp) (βsep := ![1])
    (by intro i; fin_cases i <;> norm_num [Matrix.mulVec, dotProduct])).1

-- The empty sample has the same infimum but attains it at every coefficient.
example (X : Matrix (Fin 0) (Fin 1) ℝ) (y : Fin 0 → ℝ) (β : Fin 1 → ℝ) :
    IsGLB (Set.range (logisticNLL X y)) 0 ∧ IsMinOn (logisticNLL X y) Set.univ β := by
  refine ⟨isGLB_logisticNLL_of_separable X y (fun i => Fin.elim0 i)
    (βsep := 0) (fun i => Fin.elim0 i), ?_⟩
  intro γ _
  simp [logisticNLL]

end MathlibExtTest.Probability.Statistics.LogisticRegression
