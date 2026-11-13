/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.AFTEstimation
public import MathlibExt.Probability.Distributions.GaussianCdf
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Real
open MathlibExt.Probability.Statistics.AFTEstimation

namespace MathlibExtTest.Probability.Statistics.AFTEstimation

/-! ### Observed-data law: point masses, computed from the definition -/

/-- A degenerate error gives a point mass at the linear predictor. -/
theorem logLinearLaw_dirac (η σ : ℝ) : logLinearLaw (Measure.dirac 0) η σ = Measure.dirac η := by
  rw [logLinearLaw, Measure.map_dirac' ((measurable_const_mul σ).const_add η)]
  simp

/-- `log T = 1`, `log C = 0`: the subject is censored at `0`. -/
theorem obsLaw_dirac_censored :
    obsLaw (Measure.dirac 1) (Measure.dirac 0) = Measure.dirac ((0 : ℝ), false) := by
  rw [obsLaw, Measure.dirac_prod_dirac, Measure.map_dirac' measurable_obsMap]
  norm_num [obsMap]

/-- Boundary: a tie `log T = log C = 0` counts as an observed failure. -/
theorem obsLaw_dirac_tie :
    obsLaw (Measure.dirac 0) (Measure.dirac 0) = Measure.dirac ((0 : ℝ), true) := by
  rw [obsLaw, Measure.dirac_prod_dirac, Measure.map_dirac' measurable_obsMap]
  norm_num [obsMap]

/-- The strict-decrease hypothesis on the error survival cannot be dropped: with a degenerate
error and censoring before both failure times, linear predictors `1` and `2` give the same
observed-data law. -/
theorem obsLaw_degenerate_not_identified :
    obsLaw (logLinearLaw (Measure.dirac 0) 1 1) (Measure.dirac 0) =
      obsLaw (logLinearLaw (Measure.dirac 0) 2 1) (Measure.dirac 0) := by
  rw [logLinearLaw_dirac, logLinearLaw_dirac, obsLaw, obsLaw, Measure.dirac_prod_dirac,
    Measure.dirac_prod_dirac, Measure.map_dirac' measurable_obsMap,
    Measure.map_dirac' measurable_obsMap]
  norm_num [obsMap]

/-- Consistency check of `obsLaw_prod_false` against the point-mass computation. -/
example : obsLaw (Measure.dirac 1) (Measure.dirac 0) ({0} ×ˢ {false}) = 1 := by
  rw [obsLaw_dirac_censored]
  simp

/-! ### Likelihood and score for the extreme-value (Weibull AFT) error -/

/-- Standard minimum extreme-value density `f₀(z) = exp (z - exp z)` (Weibull AFT). -/
noncomputable def evDensity (z : ℝ) : ℝ := exp (z - exp z)

/-- Its survival function `S₀(z) = exp (-exp z)`. -/
noncomputable def evSurvival (z : ℝ) : ℝ := exp (-exp z)

/-- Its density derivative `f₀'(z) = f₀(z) (1 - exp z)`. -/
noncomputable def evDensityDeriv (z : ℝ) : ℝ := exp (z - exp z) * (1 - exp z)

theorem hasDerivAt_evDensity (z : ℝ) : HasDerivAt evDensity (evDensityDeriv z) z := by
  have := ((hasDerivAt_id z).sub (hasDerivAt_exp z)).exp
  unfold evDensity evDensityDeriv
  simpa using this

theorem hasDerivAt_evSurvival (z : ℝ) : HasDerivAt evSurvival (-evDensity z) z := by
  have h := (hasDerivAt_exp z).neg.exp
  have e : -evDensity z = exp (-exp z) * -exp z := by
    rw [evDensity, exp_sub, exp_neg]
    field_simp
  rw [e]
  exact h

/-- Every observation is regular for the extreme-value error. -/
theorem regularAt_ev (z : ℝ) (δ : Bool) : RegularAt evDensity evDensityDeriv evSurvival z δ := by
  cases δ
  · exact ⟨(exp_pos _).ne', hasDerivAt_evSurvival z⟩
  · exact ⟨(exp_pos _).ne', hasDerivAt_evDensity z⟩

/-- Two subjects with an intercept-only design, both at log time `0`: one failure, one censored. -/
def yEx : Fin 2 → ℝ := ![0, 0]

/-- Subject `0` fails, subject `1` is censored. -/
def δEx : Fin 2 → Bool := ![true, false]

/-- Intercept-only covariates. -/
def xEx : Fin 2 → Fin 1 → ℝ := fun _ => ![1]

/-- At `β = 0`, `σ = 1` the likelihood is `f₀(0) S₀(0) = e⁻¹ e⁻¹`. -/
theorem likelihood_ex :
    likelihood evDensity evSurvival yEx δEx xEx 1 0 = exp (-1) * exp (-1) := by
  simp [likelihood, likContrib, Fin.prod_univ_two, yEx, δEx, evDensity, evSurvival]

/-- The log-likelihood there is `-2`, computed directly from `logLik`. -/
theorem logLik_ex : logLik evDensity evSurvival yEx δEx xEx 1 0 = -2 := by
  simp [logLik, logLikContrib, Fin.sum_univ_two, yEx, δEx, evDensity, evSurvival]
  norm_num

/-- The regression score there is `1`: residual `0` for the failure, hazard `1` for the censored
observation. -/
theorem score_ex : score evDensity evDensityDeriv evSurvival yEx δEx xEx 1 0 = ![1] := by
  ext j
  fin_cases j
  simp [score, generalizedResidual, Fin.sum_univ_two, yEx, δEx, xEx, evDensity, evDensityDeriv,
    evSurvival]

/-- The scale score there is `-1`. -/
theorem scaleScore_ex : scaleScore evDensity evDensityDeriv evSurvival yEx δEx xEx 1 0 = -1 := by
  simp [scaleScore, generalizedResidual, Fin.sum_univ_two, yEx, δEx, evDensity, evDensityDeriv,
    evSurvival]

/-- The regularity hypotheses of the score theorem are satisfiable: the gradient statement applies
to the example. -/
example : HasFDerivAt (logLik evDensity evSurvival yEx δEx xEx 1)
    (Real.dotL ![1]) 0 := by
  rw [← score_ex]
  exact hasFDerivAt_logLik yEx δEx xEx 1 0 fun i => regularAt_ev _ _

/-- Since the score is nonzero, `β = 0` is not a local maximizer of the log-likelihood. -/
example : ¬ IsLocalMax (logLik evDensity evSurvival yEx δEx xEx 1) 0 := by
  intro h
  have := score_eq_zero_of_isLocalMax yEx δEx xEx 1 0 (fun i => regularAt_ev _ _) h
  rw [score_ex] at this
  have h0 := congrFun this 0
  simp at h0

/-! ### Identifiability: the hypotheses are satisfiable, and full rank is needed -/

/-- The standard Gaussian error (log-normal AFT) has strictly decreasing survival. -/
theorem strictAnti_survival_gaussian :
    StrictAnti fun z => (gaussianReal 0 1).real (Ioi z) := by
  intro a b hab
  have h := strictMono_cdf_gaussianReal 0 one_ne_zero hab
  rw [cdf_eq_real, cdf_eq_real] at h
  simp only [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
  linarith

/-- The identity design (one subject, one coefficient) has full column rank. -/
theorem injective_mulVec_one :
    Function.Injective (Matrix.of fun _ : Fin 1 => ![(1 : ℝ)]).mulVec := by
  intro β β' h
  have := congrFun h 0
  ext j
  fin_cases j
  simpa [Matrix.mulVec, dotProduct] using this

/-- The identifiability theorem applies: log-normal AFT, one subject, censoring at `log C = 0`. -/
example {β β' : Fin 1 → ℝ} {σ σ' : ℝ} (hσ : 0 < σ) (hσ' : 0 < σ')
    (h : ∀ _ : Fin 1, obsLaw (logLinearLaw (gaussianReal 0 1) (β ⬝ᵥ ![1]) σ) (Measure.dirac 0) =
      obsLaw (logLinearLaw (gaussianReal 0 1) (β' ⬝ᵥ ![1]) σ') (Measure.dirac 0)) :
    β = β' ∧ σ = σ' :=
  identifiable (n := 1) (gaussianReal 0 1) strictAnti_survival_gaussian (fun _ => ![1])
    injective_mulVec_one (fun _ => Measure.dirac 0) (fun _ => Measure.dirac_ne_zero) hσ hσ' h

/-- A rank-deficient design: one subject with covariates `(1, 1)`. -/
def xDef : Fin 1 → Fin 2 → ℝ := fun _ => ![1, 1]

/-- Without full column rank, `β = (1, 0)` and `β' = (0, 1)` give the same observed-data law
for every error law, scale and censoring law, computed from the linear predictors. -/
theorem obsLaw_rankDeficient (μ₀ μC : Measure ℝ) (σ : ℝ) :
    obsLaw (logLinearLaw μ₀ (![1, 0] ⬝ᵥ xDef 0) σ) μC =
      obsLaw (logLinearLaw μ₀ (![0, 1] ⬝ᵥ xDef 0) σ) μC := by
  congr 2
  simp [xDef, dotProduct, Fin.sum_univ_two]

/-- Hence (`identifiable_iff`) the rank-deficient design is not injective, confirmed directly. -/
example : ¬ Function.Injective (Matrix.of xDef).mulVec := by
  intro h
  have := @h ![1, 0] ![0, 1] (by
    ext i
    fin_cases i
    simp [Matrix.mulVec, xDef, dotProduct, Fin.sum_univ_two])
  have h0 := congrFun this 0
  simp at h0

end MathlibExtTest.Probability.Statistics.AFTEstimation
