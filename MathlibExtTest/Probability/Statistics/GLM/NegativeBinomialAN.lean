/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.NegativeBinomialAN

@[expose] public section

open Finset Real Matrix ProbabilityTheory MeasureTheory Filter Topology
open scoped RealInnerProductSpace
open MathlibExt.Probability.Statistics.GLM.NegativeBinomial

namespace MathlibExtTest.Probability.Statistics.GLM.NegativeBinomialAN

/-! ### A concrete parameter: one coefficient, `β = 0`, shape `θ = 1` -/

/-- The joint parameter `(β, θ) = (0, 1)` with a single coefficient. -/
noncomputable def p₁ : NBParam (Fin 1) := WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun _ => 1))

example : nbParamShape p₁ = 1 := rfl

example : nbParamCoef p₁ = 0 := by
  funext j; rfl

/-- The parameter space with two coefficients has dimension `3` (two coefficients and the shape),
so the joint Wald, score and likelihood-ratio limits are `χ²₃` and the coefficient Wald limit is
`χ²₂`. -/
example : Module.finrank ℝ (NBParam (Fin 2)) = 3 := by
  rw [finrank_nbParam]; rfl

/-- The predictor map sends `(β, θ) = (0, 1)` to `(θ, x ⬝ᵥ β) = (1, 0)`. -/
example (x : Fin 1 → ℝ) : nbPredictorCLM x p₁ = (1, 0) := by
  rw [nbPredictorCLM_apply]
  simp [dotProduct, nbParamCoef, nbParamShape, p₁]

/-- The Fisher information operator of the model is symmetric for every reference measure. -/
example (ν : Measure ((Fin 1 → ℝ) × ℕ)) (u v : NBParam (Fin 1)) :
    ⟪nbRegFisherInfo ν p₁ u, v⟫ = ⟪u, nbRegFisherInfo ν p₁ v⟫ :=
  MathlibExt.Probability.Statistics.VectorInference.inner_fisherInformation_comm ν
    nbRegDensity p₁ u v

/-! ### The density, computed from `negBinomialReal` -/

/-- `NB(0; 1, e⁰) = (1 / 2)¹ = 1 / 2`, computed from the definition. -/
example (x : Fin 1 → ℝ) : nbRegDensity p₁ (x, 0) = 1 / 2 := by
  have hc : x ⬝ᵥ nbParamCoef p₁ = 0 := by
    simp [dotProduct, nbParamCoef, p₁]
  simp only [nbRegDensity, hc, exp_zero, negBinomialReal, ascPochhammer_zero,
    Polynomial.eval_one, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, mul_one,
    show nbParamShape p₁ = 1 from rfl]
  norm_num

/-! ### The score, computed from the closed forms -/

/-- At `y = 1 = μ` the coefficient score vanishes and the shape score is `1 - log 2`
(`nbScore`, `nbShapeScore` unfolded directly). -/
theorem nbRegScore_p₁ (x : Fin 1 → ℝ) :
    nbRegScore p₁ (x, 1) = WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun _ => 1 - log 2)) := by
  have hc : x ⬝ᵥ nbParamCoef p₁ = 0 := by
    simp [dotProduct, nbParamCoef, p₁]
  ext (j | u)
  · simp [nbRegScore, hc, nbScore, show nbParamShape p₁ = 1 from rfl]
  · simp [nbRegScore, hc, nbShapeScore, show nbParamShape p₁ = 1 from rfl]
    norm_num
    ring

/-- Non-vacuity of `score_nbRegDensity`: its hypothesis `0 < θ` holds at `p₁`, and the generic
score of the family (a `gradient`) equals the closed form there. -/
example (x : Fin 1 → ℝ) :
    MathlibExt.Probability.Statistics.VectorInference.score nbRegDensity p₁ (x, 1) =
      WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun _ => 1 - log 2)) := by
  rw [score_nbRegDensity (by simp [nbParamShape, p₁]), nbRegScore_p₁]

/-! ### Boundary of the positive-shape ball -/

/-- The parameter with shape `0` is at distance exactly `θ₀ = 1` from `p₁`, so it is not in the
open ball of radius `θ₀` used by the asymptotic theorems: the ball stays inside `θ > 0`. -/
example : (WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun _ => 0)) : NBParam (Fin 1)) ∉
    Metric.ball p₁ 1 := by
  intro h
  have := nbParamShape_pos_of_mem_ball (le_of_eq (show (1 : ℝ) = nbParamShape p₁ from rfl)) h
  simp [nbParamShape] at this

/-- A parameter strictly inside the ball has positive shape (the lemma's conclusion, checked at a
concrete point with shape `1 / 2`). -/
example : 0 < nbParamShape
    (WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun _ => 1 / 2)) : NBParam (Fin 1)) := by
  simp [nbParamShape]

/-! ### Observed information -/

/-- The averaged observed information of the empty sample is `0`. -/
example (zs : ℕ → (Fin 1 → ℝ) × ℕ) (p : NBParam (Fin 1)) : nbRegAvgObsInfo 0 zs p = 0 := by
  simp [nbRegAvgObsInfo]

/-- With one observation it is that observation's observed information. -/
example (zs : ℕ → (Fin 1 → ℝ) × ℕ) (p : NBParam (Fin 1)) :
    nbRegAvgObsInfo 1 zs p = nbRegObsInfo p (zs 0) := by
  simp [nbRegAvgObsInfo]

/-- The shape entry of the observed information at `θ = 1`, `y = 0`, `μ = 1` is
`0 - 1 + 1 / 2 + 1 / 4 = -1 / 4`: the observed shape information can be negative, so the joint
log-likelihood is not concave (cf. `NegativeBinomialDispersion`). -/
example : nbShapeObsInfo 1 0 0 = -1 / 4 := by
  norm_num [nbShapeObsInfo]

/-- The cross entry `⟪(t, 0), J (0, 1)⟫` of one observation at `p₁`, `x = 1`, `y = 3`, `t = 1`:
`-nbCross 1 3 0 = -(3 - 1) / 2² = -1 / 2`, computed with Mathlib's `inner_toEuclideanCLM` and the
entries of `nbObsInfoRow`. It is nonzero for a single count; only its mean vanishes. -/
example : ⟪nbCoefIncl (WithLp.toLp 2 (fun _ => 1)),
    nbRegObsInfo p₁ ((fun _ => 1), 3) nbShapeVec⟫ = -1 / 2 := by
  have hc : (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ nbParamCoef p₁ = 0 := by
    simp [dotProduct, nbParamCoef, p₁]
  rw [nbRegObsInfo, inner_toEuclideanCLM, hc, show nbParamShape p₁ = 1 from rfl]
  simp [dotProduct, mulVec, nbObsInfoRow, nbShapeVec, nbCross, Fintype.sum_sum_type]
  norm_num

/-! ### Coefficient-block algebra -/

example (t : EuclideanSpace ℝ (Fin 1)) : nbCoefProj (nbCoefIncl t) = t :=
  nbCoefProj_nbCoefIncl t

example (t : EuclideanSpace ℝ (Fin 1)) : nbCoefIncl t (Sum.inr ()) = 0 := rfl

example : ⟪(nbShapeVec : NBParam (Fin 1)), nbShapeVec⟫ = 1 := by
  rw [inner_nbShapeVec]; simp [nbShapeVec]

/-- A block-diagonal operator, `diag(2, 3)` on `(β, θ)`. -/
noncomputable def Idiag : NBParam (Fin 1) →L[ℝ] NBParam (Fin 1) :=
  toEuclideanCLM (𝕜 := ℝ) (diagonal (Sum.elim (fun _ => 2) (fun _ => 3)))

/-- Non-vacuity of the cross hypothesis of `apply_nbCoefIncl_of_cross`: it holds for
`diag(2, 3)`, computed entrywise. -/
theorem Idiag_cross (t : EuclideanSpace ℝ (Fin 1)) :
    ⟪Idiag nbShapeVec, nbCoefIncl t⟫ = 0 := by
  rw [real_inner_comm, Idiag, inner_toEuclideanCLM]
  simp [dotProduct, Fintype.sum_sum_type, nbShapeVec]

theorem Idiag_symm (u v : NBParam (Fin 1)) : ⟪Idiag u, v⟫ = ⟪u, Idiag v⟫ := by
  rw [real_inner_comm, Idiag, inner_toEuclideanCLM, inner_toEuclideanCLM]
  simp [dotProduct, Fintype.sum_sum_type, mulVec, diagonal, mul_comm, mul_left_comm]

/-- The block lemma at `diag(2, 3)`: `I (u, 0) = (B u, 0)`. -/
example (u : EuclideanSpace ℝ (Fin 1)) :
    Idiag (nbCoefIncl u) = nbCoefIncl (nbCoefBlock Idiag u) :=
  apply_nbCoefIncl_of_cross Idiag_symm Idiag_cross u

/-- The cross condition is a real restriction: for the all-ones matrix the cross term at `t = 1`
is `1`, not `0`. -/
example : ⟪toEuclideanCLM (𝕜 := ℝ) (of fun _ _ => (1 : ℝ) : Matrix (Fin 1 ⊕ Unit) _ ℝ)
    nbShapeVec, nbCoefIncl (WithLp.toLp 2 (fun _ => 1))⟫ = 1 := by
  rw [real_inner_comm, inner_toEuclideanCLM]
  simp [dotProduct, Fintype.sum_sum_type, mulVec, nbShapeVec]

end MathlibExtTest.Probability.Statistics.GLM.NegativeBinomialAN
