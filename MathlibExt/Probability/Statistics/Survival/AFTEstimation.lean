/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.Analysis.Calculus.DotProductGradient
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Estimation in the log-linear accelerated failure time model

In the log-linear accelerated failure time (AFT) model, the failure time `T` of a subject with
covariates `x ∈ ℝᵖ` satisfies `log T = ⟪β, x⟫ + σ ε`, with regression coefficients `β`, scale
`σ > 0` and an error `ε` of known law `μ₀` (density `f₀`, survival `S₀`). Equivalently
`T = exp ⟪β, x⟫ · T₀` with `T₀ = exp (σ ε)`: covariates rescale time. The law of `log T` is
`logLinearLaw μ₀ ⟪β, x⟫ σ`. Under independent right censoring by `C` one observes
`Y = min (log T) (log C)` and `δ = 1[T ≤ C]`, with law `obsLaw`; ties count as events, as in
`MathlibExt.Probability.Statistics.Censoring`. The discrete-grid analogue of `obsLaw` is
`MathlibExt.Probability.Statistics.Censoring.censoredObsLaw` (in `IdentifiableHorizon`).

## Main results

* **Observed-data law** (independent censoring, `G` the law of `log C`):
  `obsLaw_Ioi_prod_univ` (`P(Y > y) = P(log T > y) G(y, ∞)`), `obsLaw_prod_false`
  (`P(Y ∈ A, δ = 0) = ∫_A P(log T > c) dG(c)`), `obsLaw_prod_true`
  (`P(Y ∈ A, δ = 1) = ∫_A G[t, ∞) d law(log T)(t)`).
* **Likelihood factors.** `logLinearLaw_withDensity`: `log T` has density
  `σ⁻¹ f₀((t - η) / σ)`. Hence `obsLaw_logLinearLaw_prod_true` and
  `obsLaw_logLinearLaw_prod_false`: the parameter enters the observed-data law only through
  `likContrib`, which is `f₀(z) / σ` for an event and `S₀(z)` for a censored observation,
  `z = (y - η) / σ`. The censoring factors `G[y, ∞)` and `dG` do not involve `(β, σ)`, so they
  drop out of the likelihood (non-informative censoring).
* **Censored likelihood.** `likelihood` is `∏ᵢ (f₀(zᵢ) / σ)^{δᵢ} S₀(zᵢ)^{1 - δᵢ}` and `logLik`
  is its logarithm (`log_likelihood`).
* **Score.** With the generalized residual `r(z, δ)` (`generalizedResidual`: `-f₀'/f₀` for
  events, the error hazard `f₀/S₀` for censored observations), the regression score
  `U_β = σ⁻¹ ∑ᵢ r(zᵢ, δᵢ) xᵢ` is the gradient of `ℓ(·, σ)` (`hasFDerivAt_logLik`,
  `hasGradientAt_logLik`) and the scale score `U_σ = σ⁻¹ ∑ᵢ (zᵢ rᵢ - δᵢ)` is `∂ℓ/∂σ`
  (`hasDerivAt_logLik_scale`). A regular local maximizer solves the score equations
  (`score_eq_zero_of_isLocalMax`, `scaleScore_eq_zero_of_isLocalMax`), and a regular joint
  local maximizer in `(β, σ)` solves both (`score_eq_zero_and_scaleScore_eq_zero`).
* **Identifiability.** If the error survival is strictly decreasing and each censoring law is a
  nonzero finite measure free of the parameters, the observed-data law of one subject determines
  `(⟪β, x⟫, σ)` (`eq_of_obsLaw_eq`). With a full-column-rank design the observed-data laws of all
  subjects determine `(β, σ)` (`identifiable`), and at a fixed scale full column rank is
  necessary and sufficient for `β` to be identified (`identifiable_iff`).

## Scope

The censoring law of each subject may depend on its covariates but is held fixed when the
parameters vary. Identification when the censoring law is an unknown nuisance that may also
change (which needs the observed-data identification of the hazard of `T`) is not treated, nor
are consistency, asymptotic normality or uniqueness of the maximum likelihood estimator.
`f₀` and `S₀` in the likelihood are arbitrary functions; the theorems that link them to `μ₀` say
so in their hypotheses.

## References

* J. D. Kalbfleisch and R. L. Prentice, *The Statistical Analysis of Failure Time Data*, 2nd ed.,
  Wiley (2002), §2.3 (the log-linear AFT model `log T = x'β + σW`) and Chapter 3 (likelihood
  under independent censoring, parametric regression).
* J. F. Lawless, *Statistical Models and Methods for Lifetime Data*, 2nd ed., Wiley (2003),
  §2.2 (the censored-data likelihood `∏ f(yᵢ)^{δᵢ} S(yᵢ)^{1 - δᵢ}`) and Chapter 6
  (log-location-scale regression: likelihood and score equations).
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.AFTEstimation

open MeasureTheory Set Real

open scoped ENNReal

noncomputable section

/-- The law of `log T = η + σ ε` for an error `ε ~ μ₀`. -/
def logLinearLaw (μ₀ : Measure ℝ) (η σ : ℝ) : Measure ℝ :=
  μ₀.map fun e => η + σ * e

/-- A finite error law gives a finite law of `log T`. -/
instance isFiniteMeasure_logLinearLaw (μ₀ : Measure ℝ) [IsFiniteMeasure μ₀] (η σ : ℝ) :
    IsFiniteMeasure (logLinearLaw μ₀ η σ) :=
  inferInstanceAs (IsFiniteMeasure (μ₀.map _))

/-- The observation map `(log T, log C) ↦ (min (log T) (log C), 1[T ≤ C])`. -/
def obsMap (ω : ℝ × ℝ) : ℝ × Bool :=
  (min ω.1 ω.2, decide (ω.1 ≤ ω.2))

/-- The observation map is measurable. -/
theorem measurable_obsMap : Measurable obsMap := by
  have h : (fun ω : ℝ × ℝ => decide (ω.1 ≤ ω.2)) ⁻¹' {true} = {ω | ω.1 ≤ ω.2} := by
    ext ω; simp
  exact (measurable_fst.min measurable_snd).prodMk
    (measurable_to_bool (h ▸ measurableSet_le measurable_fst measurable_snd))

/-- The law of the observed data `(Y, δ) = (min (log T) (log C), 1[T ≤ C])` when the log failure
time has law `μT` and the independent log censoring time has law `μC`. -/
def obsLaw (μT μC : Measure ℝ) : Measure (ℝ × Bool) :=
  (μT.prod μC).map obsMap

section ObservedLaw

variable (μT μC : Measure ℝ) [SFinite μT] [SFinite μC]

omit [SFinite μT] in
/-- Under independent censoring `P(Y > y) = P(log T > y) P(log C > y)`. -/
theorem obsLaw_Ioi_prod_univ (y : ℝ) :
    obsLaw μT μC (Ioi y ×ˢ univ) = μT (Ioi y) * μC (Ioi y) := by
  rw [obsLaw, Measure.map_apply measurable_obsMap (measurableSet_Ioi.prod MeasurableSet.univ)]
  have : obsMap ⁻¹' (Ioi y ×ˢ univ) = Ioi y ×ˢ Ioi y := by
    ext ω
    simp only [obsMap, Set.mem_preimage, Set.mem_prod, mem_Ioi, mem_univ, and_true, lt_min_iff]
  rw [this, Measure.prod_prod]

/-- **Censored observations**: `P(Y ∈ A, δ = 0) = ∫_A P(log T > c) dG(c)`, the survival of
`log T` at the censoring time integrated against the censoring law `G = μC`. -/
theorem obsLaw_prod_false {A : Set ℝ} (hA : MeasurableSet A) :
    obsLaw μT μC (A ×ˢ {false}) = ∫⁻ c in A, μT (Ioi c) ∂μC := by
  have hs : obsMap ⁻¹' (A ×ˢ {false}) = {ω | ω.2 ∈ A ∧ ω.2 < ω.1} := by
    ext ω
    simp only [obsMap, Set.mem_preimage, Set.mem_prod, mem_singleton_iff, decide_eq_false_iff_not,
      not_le]
    change _ ↔ _ ∧ _
    constructor
    · rintro ⟨h1, h2⟩; rw [min_eq_right h2.le] at h1; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; rw [min_eq_right h2.le]; exact ⟨h1, h2⟩
  have hm : MeasurableSet {ω : ℝ × ℝ | ω.2 ∈ A ∧ ω.2 < ω.1} :=
    (measurable_snd hA).inter (measurableSet_lt measurable_snd measurable_fst)
  rw [obsLaw, Measure.map_apply measurable_obsMap (hA.prod (measurableSet_singleton _)), hs,
    Measure.prod_apply_symm hm, ← lintegral_indicator hA]
  refine lintegral_congr fun c => ?_
  by_cases hc : c ∈ A
  · simp only [indicator_of_mem hc]
    congr 1; ext t; simp [hc]
  · simp [hc]

omit [SFinite μT] in
/-- **Observed failures**: `P(Y ∈ A, δ = 1) = ∫_A G[t, ∞) dμT(t)`, the censoring survival at the
failure time integrated against the law `μT` of `log T` (ties count as failures). -/
theorem obsLaw_prod_true {A : Set ℝ} (hA : MeasurableSet A) :
    obsLaw μT μC (A ×ˢ {true}) = ∫⁻ t in A, μC (Ici t) ∂μT := by
  have hs : obsMap ⁻¹' (A ×ˢ {true}) = {ω | ω.1 ∈ A ∧ ω.1 ≤ ω.2} := by
    ext ω
    simp only [obsMap, Set.mem_preimage, Set.mem_prod, mem_singleton_iff, decide_eq_true_eq]
    change _ ↔ _ ∧ _
    constructor
    · rintro ⟨h1, h2⟩; rw [min_eq_left h2] at h1; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; rw [min_eq_left h2]; exact ⟨h1, h2⟩
  have hm : MeasurableSet {ω : ℝ × ℝ | ω.1 ∈ A ∧ ω.1 ≤ ω.2} :=
    (measurable_fst hA).inter (measurableSet_le measurable_fst measurable_snd)
  rw [obsLaw, Measure.map_apply measurable_obsMap (hA.prod (measurableSet_singleton _)), hs,
    Measure.prod_apply hm, ← lintegral_indicator hA]
  refine lintegral_congr fun t => ?_
  by_cases ht : t ∈ A
  · simp only [indicator_of_mem ht]
    congr 1; ext c; simp [ht]
  · simp [ht]

end ObservedLaw

/-- **Survival of the log-linear law**: `P(log T > y) = P(ε > (y - η) / σ)` for `σ > 0`. -/
theorem logLinearLaw_Ioi (μ₀ : Measure ℝ) (η : ℝ) {σ : ℝ} (hσ : 0 < σ) (y : ℝ) :
    logLinearLaw μ₀ η σ (Ioi y) = μ₀ (Ioi ((y - η) / σ)) := by
  have hm : Measurable fun e : ℝ => η + σ * e := (measurable_const_mul σ).const_add η
  rw [logLinearLaw, Measure.map_apply hm measurableSet_Ioi]
  congr 1
  ext e
  simp only [mem_preimage, mem_Ioi, div_lt_iff₀ hσ]
  constructor <;> intro h <;> linarith

/-! ### The censored likelihood -/

/-- The likelihood contribution of one observation `(y, δ)` with linear predictor `η` and scale
`σ`: the density `f₀(z) / σ` of `log T` at `y` for an observed failure (`δ = true`) and the
survival `S₀(z)` for a censored one, where `z = (y - η) / σ` is the standardized residual. -/
def likContrib (f₀ S₀ : ℝ → ℝ) (σ η y : ℝ) (δ : Bool) : ℝ :=
  if δ then f₀ ((y - η) / σ) / σ else S₀ ((y - η) / σ)

/-- The log-likelihood contribution of one observation: `log f₀(z) - log σ` for an observed
failure and `log S₀(z)` for a censored one, with `z = (y - η) / σ`. -/
def logLikContrib (f₀ S₀ : ℝ → ℝ) (σ η y : ℝ) (δ : Bool) : ℝ :=
  if δ then log (f₀ ((y - η) / σ)) - log σ else log (S₀ ((y - η) / σ))

variable {n p : ℕ}

/-- The censored log-linear AFT likelihood `∏ᵢ (f₀(zᵢ) / σ)^{δᵢ} S₀(zᵢ)^{1 - δᵢ}` with
`zᵢ = (yᵢ - ⟪β, xᵢ⟫) / σ`, for log follow-up times `y`, event flags `δ` and covariates `x`. -/
def likelihood (f₀ S₀ : ℝ → ℝ) (y : Fin n → ℝ) (δ : Fin n → Bool) (x : Fin n → Fin p → ℝ)
    (σ : ℝ) (β : Fin p → ℝ) : ℝ :=
  ∏ i, likContrib f₀ S₀ σ (β ⬝ᵥ x i) (y i) (δ i)

/-- The censored log-linear AFT log-likelihood
`ℓ(β, σ) = ∑ᵢ δᵢ (log f₀(zᵢ) - log σ) + (1 - δᵢ) log S₀(zᵢ)`, `zᵢ = (yᵢ - ⟪β, xᵢ⟫) / σ`. -/
def logLik (f₀ S₀ : ℝ → ℝ) (y : Fin n → ℝ) (δ : Fin n → Bool) (x : Fin n → Fin p → ℝ)
    (σ : ℝ) (β : Fin p → ℝ) : ℝ :=
  ∑ i, logLikContrib f₀ S₀ σ (β ⬝ᵥ x i) (y i) (δ i)

/-- The log of a nonzero likelihood contribution is the log-likelihood contribution. -/
theorem log_likContrib (f₀ S₀ : ℝ → ℝ) {σ : ℝ} (hσ : 0 < σ) (η y : ℝ) (δ : Bool)
    (h : likContrib f₀ S₀ σ η y δ ≠ 0) :
    log (likContrib f₀ S₀ σ η y δ) = logLikContrib f₀ S₀ σ η y δ := by
  cases δ
  · rfl
  · have hf : f₀ ((y - η) / σ) ≠ 0 := fun h0 => h (by simp [likContrib, h0])
    simp only [likContrib, logLikContrib, ite_true]
    exact log_div hf hσ.ne'

/-- The log of the censored likelihood is the censored log-likelihood (when no factor
vanishes). -/
theorem log_likelihood (f₀ S₀ : ℝ → ℝ) (y : Fin n → ℝ) (δ : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) {σ : ℝ} (hσ : 0 < σ) (β : Fin p → ℝ)
    (h : ∀ i, likContrib f₀ S₀ σ (β ⬝ᵥ x i) (y i) (δ i) ≠ 0) :
    log (likelihood f₀ S₀ y δ x σ β) = logLik f₀ S₀ y δ x σ β := by
  rw [likelihood, log_prod fun i _ => h i, logLik]
  exact Finset.sum_congr rfl fun i _ => log_likContrib f₀ S₀ hσ _ _ _ (h i)

/-! ### The score -/

/-- The **generalized residual** `r(z, δ) = -∂_z (log contribution)`: `-f₀'(z) / f₀(z)` for an
observed failure and the error hazard `f₀(z) / S₀(z)` for a censored observation. -/
def generalizedResidual (f₀ f₀' S₀ : ℝ → ℝ) (z : ℝ) (δ : Bool) : ℝ :=
  if δ then -(f₀' z / f₀ z) else f₀ z / S₀ z

/-- The regularity needed to differentiate one contribution at the standardized residual `z`:
`f₀(z) ≠ 0` with derivative `f₀'(z)` for an observed failure, and `S₀(z) ≠ 0` with
`S₀' = -f₀` at `z` for a censored observation. -/
def RegularAt (f₀ f₀' S₀ : ℝ → ℝ) (z : ℝ) (δ : Bool) : Prop :=
  if δ then f₀ z ≠ 0 ∧ HasDerivAt f₀ (f₀' z) z else S₀ z ≠ 0 ∧ HasDerivAt S₀ (-f₀ z) z

/-- The **regression score** `U_β = σ⁻¹ ∑ᵢ r(zᵢ, δᵢ) xᵢ`. -/
def score (f₀ f₀' S₀ : ℝ → ℝ) (y : Fin n → ℝ) (δ : Fin n → Bool) (x : Fin n → Fin p → ℝ)
    (σ : ℝ) (β : Fin p → ℝ) : Fin p → ℝ :=
  σ⁻¹ • ∑ i, generalizedResidual f₀ f₀' S₀ ((y i - β ⬝ᵥ x i) / σ) (δ i) • x i

/-- The **scale score** `U_σ = σ⁻¹ ∑ᵢ (zᵢ r(zᵢ, δᵢ) - δᵢ)`. -/
def scaleScore (f₀ f₀' S₀ : ℝ → ℝ) (y : Fin n → ℝ) (δ : Fin n → Bool) (x : Fin n → Fin p → ℝ)
    (σ : ℝ) (β : Fin p → ℝ) : ℝ :=
  σ⁻¹ * ∑ i, ((y i - β ⬝ᵥ x i) / σ * generalizedResidual f₀ f₀' S₀ ((y i - β ⬝ᵥ x i) / σ) (δ i) -
    if δ i then 1 else 0)

/-- The log contribution as a function of the standardized residual. -/
private def logContribZ (f₀ S₀ : ℝ → ℝ) (δ : Bool) (z : ℝ) : ℝ :=
  if δ then log (f₀ z) else log (S₀ z)

private lemma logLikContrib_eq (f₀ S₀ : ℝ → ℝ) (σ η y : ℝ) (δ : Bool) :
    logLikContrib f₀ S₀ σ η y δ =
      logContribZ f₀ S₀ δ ((y - η) / σ) - if δ then log σ else 0 := by
  cases δ <;> simp [logLikContrib, logContribZ]

private lemma hasDerivAt_logContribZ {f₀ f₀' S₀ : ℝ → ℝ} {z : ℝ} {δ : Bool}
    (h : RegularAt f₀ f₀' S₀ z δ) :
    HasDerivAt (logContribZ f₀ S₀ δ) (-generalizedResidual f₀ f₀' S₀ z δ) z := by
  cases δ
  · simp only [RegularAt, Bool.false_eq_true, ite_false] at h
    rw [show -generalizedResidual f₀ f₀' S₀ z false = -f₀ z / S₀ z by
      simp [generalizedResidual, neg_div]]
    exact h.2.log h.1
  · simp only [RegularAt, ite_true] at h
    rw [show -generalizedResidual f₀ f₀' S₀ z true = f₀' z / f₀ z by simp [generalizedResidual]]
    exact h.2.log h.1

private lemma hasFDerivAt_logLikContrib {f₀ f₀' S₀ : ℝ → ℝ} (σ y : ℝ) (δ : Bool)
    (x β : Fin p → ℝ) (h : RegularAt f₀ f₀' S₀ ((y - β ⬝ᵥ x) / σ) δ) :
    HasFDerivAt (fun β => logLikContrib f₀ S₀ σ (β ⬝ᵥ x) y δ)
      (Real.dotL ((σ⁻¹ * generalizedResidual f₀ f₀' S₀ ((y - β ⬝ᵥ x) / σ) δ) • x)) β := by
  have hu : HasFDerivAt (fun β : Fin p → ℝ => (y - β ⬝ᵥ x) / σ)
      (σ⁻¹ • -Real.dotL x) β := by
    have := ((Real.hasFDerivAt_dotProduct x β).const_sub y).const_mul σ⁻¹
    convert this using 1
    funext b; rw [div_eq_inv_mul]
  have hc := (hasDerivAt_logContribZ h).comp_hasFDerivAt β hu
  have he : (fun β => logLikContrib f₀ S₀ σ (β ⬝ᵥ x) y δ) =
      fun β => logContribZ f₀ S₀ δ ((y - β ⬝ᵥ x) / σ) - if δ then log σ else 0 := by
    funext b; exact logLikContrib_eq f₀ S₀ σ _ y δ
  rw [he]
  refine (hc.sub_const (if δ then log σ else 0)).congr_fderiv ?_
  ext v
  simp only [Real.dotL_apply, dotProduct_smul, smul_eq_mul, FunLike.coe_smul,
    Pi.smul_apply]
  rw [show (-Real.dotL x) v = -(v ⬝ᵥ x) by simp]
  ring

/-- **The regression score is the gradient of the censored log-likelihood** (Fréchet form): at a
point where every contribution is regular, `ℓ(·, σ)` has derivative `v ↦ ⟪v, U_β⟫`. -/
theorem hasFDerivAt_logLik {f₀ f₀' S₀ : ℝ → ℝ} (y : Fin n → ℝ) (δ : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) (σ : ℝ) (β : Fin p → ℝ)
    (h : ∀ i, RegularAt f₀ f₀' S₀ ((y i - β ⬝ᵥ x i) / σ) (δ i)) :
    HasFDerivAt (logLik f₀ S₀ y δ x σ) (Real.dotL (score f₀ f₀' S₀ y δ x σ β)) β := by
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    hasFDerivAt_logLikContrib σ (y i) (δ i) (x i) β (h i)
  convert hs using 1
  · funext b; simp [logLik]
  · ext v
    simp only [score, Real.dotL_apply, FunLike.coe_sum, Finset.sum_apply,
      dotProduct_smul, dotProduct_sum, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- **The regression score is the gradient of the censored log-likelihood**, as a Mathlib
gradient on `EuclideanSpace ℝ (Fin p)`. -/
theorem hasGradientAt_logLik {f₀ f₀' S₀ : ℝ → ℝ} (y : Fin n → ℝ) (δ : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) (σ : ℝ) (β : Fin p → ℝ)
    (h : ∀ i, RegularAt f₀ f₀' S₀ ((y i - β ⬝ᵥ x i) / σ) (δ i)) :
    HasGradientAt (fun b : EuclideanSpace ℝ (Fin p) => logLik f₀ S₀ y δ x σ b.ofLp)
      (WithLp.toLp 2 (score f₀ f₀' S₀ y δ x σ β)) (WithLp.toLp 2 β) :=
  Real.hasGradientAt_ofLp (hasFDerivAt_logLik y δ x σ β h)

private lemma hasDerivAt_logLikContrib_scale {f₀ f₀' S₀ : ℝ → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (η y : ℝ) (δ : Bool) (h : RegularAt f₀ f₀' S₀ ((y - η) / σ) δ) :
    HasDerivAt (fun s => logLikContrib f₀ S₀ s η y δ)
      (σ⁻¹ * ((y - η) / σ * generalizedResidual f₀ f₀' S₀ ((y - η) / σ) δ -
        if δ then 1 else 0)) σ := by
  have hu : HasDerivAt (fun s : ℝ => (y - η) / s) ((y - η) * -(σ ^ 2)⁻¹) σ := by
    have := (hasDerivAt_inv hσ.ne').const_mul (y - η)
    convert this using 1
    funext s; rw [div_eq_mul_inv]
  have hc := (hasDerivAt_logContribZ h).comp σ hu
  have he : (fun s => logLikContrib f₀ S₀ s η y δ) =
      fun s => logContribZ f₀ S₀ δ ((y - η) / s) - if δ then log s else 0 := by
    funext s; exact logLikContrib_eq f₀ S₀ s η y δ
  rw [he]
  cases δ
  · simp only [Bool.false_eq_true, ite_false, sub_zero]
    exact hc.congr_deriv (by field_simp)
  · simp only [ite_true]
    exact (hc.sub (Real.hasDerivAt_log hσ.ne')).congr_deriv (by field_simp)

/-- **The scale score is the `σ`-derivative of the censored log-likelihood.** -/
theorem hasDerivAt_logLik_scale {f₀ f₀' S₀ : ℝ → ℝ} (y : Fin n → ℝ) (δ : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) {σ : ℝ} (hσ : 0 < σ) (β : Fin p → ℝ)
    (h : ∀ i, RegularAt f₀ f₀' S₀ ((y i - β ⬝ᵥ x i) / σ) (δ i)) :
    HasDerivAt (fun s => logLik f₀ S₀ y δ x s β) (scaleScore f₀ f₀' S₀ y δ x σ β) σ := by
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    hasDerivAt_logLikContrib_scale hσ (β ⬝ᵥ x i) (y i) (δ i) (h i)
  convert hs using 1
  · funext s; simp [logLik]
  · simp only [scaleScore, Finset.mul_sum]

/-- **Score equations.** A regular local maximizer `β̂` of `ℓ(·, σ)` solves `U_β(β̂) = 0`. -/
theorem score_eq_zero_of_isLocalMax {f₀ f₀' S₀ : ℝ → ℝ} (y : Fin n → ℝ) (δ : Fin n → Bool)
    (x : Fin n → Fin p → ℝ) (σ : ℝ) (β : Fin p → ℝ)
    (h : ∀ i, RegularAt f₀ f₀' S₀ ((y i - β ⬝ᵥ x i) / σ) (δ i))
    (hmax : IsLocalMax (logLik f₀ S₀ y δ x σ) β) :
    score f₀ f₀' S₀ y δ x σ β = 0 := by
  have h0 := hmax.hasFDerivAt_eq_zero (hasFDerivAt_logLik y δ x σ β h)
  have := congrArg (fun L : (Fin p → ℝ) →L[ℝ] ℝ => L (score f₀ f₀' S₀ y δ x σ β)) h0
  simpa [Real.dotL_apply, dotProduct_self_eq_zero] using this

/-- **Scale score equation.** A regular local maximizer `σ̂ > 0` of `ℓ(β, ·)` solves
`U_σ(σ̂) = 0`. -/
theorem scaleScore_eq_zero_of_isLocalMax {f₀ f₀' S₀ : ℝ → ℝ} (y : Fin n → ℝ)
    (δ : Fin n → Bool) (x : Fin n → Fin p → ℝ) {σ : ℝ} (hσ : 0 < σ) (β : Fin p → ℝ)
    (h : ∀ i, RegularAt f₀ f₀' S₀ ((y i - β ⬝ᵥ x i) / σ) (δ i))
    (hmax : IsLocalMax (fun s => logLik f₀ S₀ y δ x s β) σ) :
    scaleScore f₀ f₀' S₀ y δ x σ β = 0 :=
  hmax.hasDerivAt_eq_zero (hasDerivAt_logLik_scale y δ x hσ β h)

/-- **Joint score equations.** A regular joint local maximizer `(β̂, σ̂)`, `σ̂ > 0`, of the
censored log-likelihood solves `U_β = 0` and `U_σ = 0`. -/
theorem score_eq_zero_and_scaleScore_eq_zero {f₀ f₀' S₀ : ℝ → ℝ} (y : Fin n → ℝ)
    (δ : Fin n → Bool) (x : Fin n → Fin p → ℝ) {σ : ℝ} (hσ : 0 < σ) (β : Fin p → ℝ)
    (h : ∀ i, RegularAt f₀ f₀' S₀ ((y i - β ⬝ᵥ x i) / σ) (δ i))
    (hmax : IsLocalMax (fun q : (Fin p → ℝ) × ℝ => logLik f₀ S₀ y δ x q.2 q.1) (β, σ)) :
    score f₀ f₀' S₀ y δ x σ β = 0 ∧ scaleScore f₀ f₀' S₀ y δ x σ β = 0 :=
  ⟨score_eq_zero_of_isLocalMax y δ x σ β h
      (hmax.comp_continuous (g := fun b => (b, σ)) (by fun_prop)),
    scaleScore_eq_zero_of_isLocalMax y δ x hσ β h
      (hmax.comp_continuous (g := fun s => (β, s)) (by fun_prop))⟩

/-! ### The likelihood factors of the observed-data law -/

/-- **Censored factor.** If `S₀` is the survival function of the error law `μ₀`, the censored
likelihood contribution at `y` is `P(log T > y)` under the log-linear law. -/
theorem likContrib_false_eq (f₀ : ℝ → ℝ) (μ₀ : Measure ℝ) (η : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (y : ℝ) :
    likContrib f₀ (fun z => μ₀.real (Ioi z)) σ η y false = (logLinearLaw μ₀ η σ).real (Ioi y) := by
  simp [likContrib, measureReal_def, logLinearLaw_Ioi μ₀ η hσ]

/-- **The censored part of the observed-data law is the censored likelihood factor integrated
against the censoring law**: `P(Y ∈ A, δ = 0) = ∫_A S₀((c - η) / σ) dG(c)`. -/
theorem obsLaw_logLinearLaw_prod_false (f₀ : ℝ → ℝ) (μ₀ : Measure ℝ) [IsFiniteMeasure μ₀]
    (μC : Measure ℝ) [SFinite μC] (η : ℝ) {σ : ℝ} (hσ : 0 < σ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    obsLaw (logLinearLaw μ₀ η σ) μC (A ×ˢ {false}) =
      ∫⁻ c in A, ENNReal.ofReal (likContrib f₀ (fun z => μ₀.real (Ioi z)) σ η c false) ∂μC := by
  rw [obsLaw_prod_false _ _ hA]
  refine lintegral_congr fun c => ?_
  rw [likContrib_false_eq f₀ μ₀ η hσ, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

private lemma map_volume_affine (η : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    Measure.map (fun e : ℝ => η + σ * e) volume = ENNReal.ofReal σ⁻¹ • volume := by
  have he : (fun e : ℝ => η + σ * e) = (fun t => η + t) ∘ fun e => σ * e := rfl
  rw [he, ← Measure.map_map (measurable_const_add η) (measurable_const_mul σ),
    Real.map_volume_mul_left hσ.ne', Measure.map_smul, map_add_left_eq_self,
    abs_of_pos (inv_pos.2 hσ)]
  exact (measurable_const_add η).aemeasurable

/-- **Density of the log-linear law.** If the error law has Lebesgue density `g`, then
`log T = η + σ ε` has density `t ↦ σ⁻¹ g((t - η) / σ)`. -/
theorem logLinearLaw_withDensity {g : ℝ → ℝ≥0∞} (hg : Measurable g) (η : ℝ) {σ : ℝ}
    (hσ : 0 < σ) :
    logLinearLaw (volume.withDensity g) η σ =
      volume.withDensity fun t => ENNReal.ofReal σ⁻¹ * g ((t - η) / σ) := by
  have hm : Measurable fun e : ℝ => η + σ * e := (measurable_const_mul σ).const_add η
  have hG : Measurable fun t => g ((t - η) / σ) :=
    hg.comp ((measurable_id.sub_const η).div_const σ)
  ext s hs
  rw [logLinearLaw, Measure.map_apply hm hs, withDensity_apply _ (hm hs), withDensity_apply _ hs,
    lintegral_const_mul _ hG, ← lintegral_indicator hs, ← lintegral_indicator (hm hs),
    show ∀ F : ℝ → ℝ≥0∞, ENNReal.ofReal σ⁻¹ * ∫⁻ a, F a =
        ∫⁻ a, F a ∂(ENNReal.ofReal σ⁻¹ • volume) from
      fun F => by rw [lintegral_smul_measure, smul_eq_mul],
    ← map_volume_affine η hσ, lintegral_map (hG.indicator hs) hm]
  refine lintegral_congr fun e => ?_
  have hpre : e ∈ (fun e : ℝ => η + σ * e) ⁻¹' s ↔ η + σ * e ∈ s := Iff.rfl
  by_cases he : η + σ * e ∈ s
  · rw [indicator_of_mem he, indicator_of_mem (hpre.2 he)]
    congr 1
    field_simp
    ring
  · rw [indicator_of_notMem he, indicator_of_notMem (mt hpre.1 he)]

/-- **The event part of the observed-data law is the event likelihood factor times the censoring
survival**: if the error law has density `f₀`, then
`P(Y ∈ A, δ = 1) = ∫_A (f₀((t - η) / σ) / σ) G([t, ∞)) dt`. -/
theorem obsLaw_logLinearLaw_prod_true {f₀ : ℝ → ℝ} (hf₀ : Measurable f₀) (S₀ : ℝ → ℝ)
    (μC : Measure ℝ) [SFinite μC] (η : ℝ) {σ : ℝ} (hσ : 0 < σ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    obsLaw (logLinearLaw (volume.withDensity fun e => ENNReal.ofReal (f₀ e)) η σ) μC
        (A ×ˢ {true}) =
      ∫⁻ t in A, ENNReal.ofReal (likContrib f₀ S₀ σ η t true) * μC (Ici t) := by
  have hg : Measurable fun e => ENNReal.ofReal (f₀ e) := hf₀.ennreal_ofReal
  have hC : Measurable fun t : ℝ => μC (Ici t) :=
    Antitone.measurable fun a b hab => measure_mono (Ici_subset_Ici.2 hab)
  rw [obsLaw_prod_true _ _ hA, logLinearLaw_withDensity hg η hσ,
    setLIntegral_withDensity_eq_setLIntegral_mul _ ?_ hC hA]
  · refine setLIntegral_congr_fun hA fun t _ => ?_
    simp only [Pi.mul_apply, likContrib, ite_true, div_eq_inv_mul (f₀ _) σ,
      ENNReal.ofReal_mul (inv_nonneg.2 hσ.le)]
  · exact measurable_const.mul (hg.comp ((measurable_id.sub_const η).div_const σ))

/-! ### Identifiability -/

private lemma exists_Ioi_ne_zero (μC : Measure ℝ) (hC : μC ≠ 0) : ∃ y, μC (Ioi y) ≠ 0 := by
  by_contra hcon
  simp only [ne_eq, not_exists, not_not] at hcon
  apply hC
  rw [← Measure.measure_univ_eq_zero]
  refine tendsto_nhds_unique (tendsto_measure_Ici_atBot μC) ?_
  refine tendsto_const_nhds.congr fun t => ?_
  exact (measure_mono_null (Ici_subset_Ioi.2 (sub_one_lt t)) (hcon (t - 1))).symm

/-- **Identifiability for one covariate value.** Let the error law `μ₀` be finite with strictly
decreasing survival function (e.g. any law with an everywhere positive density), and let the log
censoring time have a nonzero finite law `μC` not depending on the parameters. If the log-linear
models `(η, σ)` and `(η', σ')` give the same observed-data law, then `η = η'` and `σ = σ'`. -/
theorem eq_of_obsLaw_eq (μ₀ : Measure ℝ) [IsFiniteMeasure μ₀]
    (hS : StrictAnti fun z => μ₀.real (Ioi z)) (μC : Measure ℝ) [IsFiniteMeasure μC]
    (hC : μC ≠ 0) {η η' σ σ' : ℝ} (hσ : 0 < σ) (hσ' : 0 < σ')
    (h : obsLaw (logLinearLaw μ₀ η σ) μC = obsLaw (logLinearLaw μ₀ η' σ') μC) :
    η = η' ∧ σ = σ' := by
  obtain ⟨y₀, hy₀⟩ := exists_Ioi_ne_zero μC hC
  have key : ∀ y ≤ y₀, (y - η) / σ = (y - η') / σ' := by
    intro y hy
    have hCy : μC (Ioi y) ≠ 0 := fun h0 => hy₀ (measure_mono_null (Ioi_subset_Ioi hy) h0)
    have h1 := congrArg (fun ν : Measure (ℝ × Bool) => ν (Ioi y ×ˢ univ)) h
    simp only [obsLaw_Ioi_prod_univ, logLinearLaw_Ioi μ₀ _ hσ, logLinearLaw_Ioi μ₀ _ hσ'] at h1
    have h2 := (ENNReal.mul_left_inj hCy (measure_ne_top μC _)).1 h1
    exact hS.injective (by simp only [measureReal_def, h2])
  have e1 := key y₀ le_rfl
  have e2 := key (y₀ - 1) (by linarith)
  have hinv : σ⁻¹ = σ'⁻¹ := by
    have : (y₀ - η) / σ - (y₀ - 1 - η) / σ = (y₀ - η') / σ' - (y₀ - 1 - η') / σ' := by
      rw [e1, e2]
    rw [← sub_div, ← sub_div] at this
    simpa using this
  have hσσ : σ = σ' := inv_injective hinv
  subst hσσ
  refine ⟨?_, rfl⟩
  have := (div_left_inj' hσ.ne').1 e1
  linarith

/-- **Identifiability of the regression coefficients and the scale.** In the log-linear AFT
model `log Tᵢ = ⟪β, xᵢ⟫ + σ εᵢ` with independent censoring, suppose the error law has strictly
decreasing survival, each subject's log censoring law is nonzero, finite and free of `(β, σ)`, and
the design has full column rank (`β ↦ (⟪β, xᵢ⟫)ᵢ` is injective). If `(β, σ)` and `(β', σ')` give
the same observed-data law for every subject, then `β = β'` and `σ = σ'`. -/
theorem identifiable {n p : ℕ} [NeZero n] (μ₀ : Measure ℝ) [IsFiniteMeasure μ₀]
    (hS : StrictAnti fun z => μ₀.real (Ioi z)) (x : Fin n → Fin p → ℝ)
    (hx : Function.Injective (Matrix.of x).mulVec) (μC : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (μC i)] (hC : ∀ i, μC i ≠ 0) {β β' : Fin p → ℝ} {σ σ' : ℝ}
    (hσ : 0 < σ) (hσ' : 0 < σ')
    (h : ∀ i, obsLaw (logLinearLaw μ₀ (β ⬝ᵥ x i) σ) (μC i) =
      obsLaw (logLinearLaw μ₀ (β' ⬝ᵥ x i) σ') (μC i)) :
    β = β' ∧ σ = σ' := by
  have hi := fun i => eq_of_obsLaw_eq μ₀ hS (μC i) (hC i) hσ hσ' (h i)
  refine ⟨hx (funext fun i => ?_), (hi 0).2⟩
  simp only [Matrix.mulVec, Matrix.of_apply]
  rw [dotProduct_comm, (hi i).1, dotProduct_comm]

/-- **Full column rank is necessary and sufficient** for the regression coefficients to be
identified (at a common known scale `σ > 0`) from the observed-data laws. -/
theorem identifiable_iff {n p : ℕ} (μ₀ : Measure ℝ) [IsFiniteMeasure μ₀]
    (hS : StrictAnti fun z => μ₀.real (Ioi z)) (x : Fin n → Fin p → ℝ)
    (μC : Fin n → Measure ℝ) [∀ i, IsFiniteMeasure (μC i)] (hC : ∀ i, μC i ≠ 0) {σ : ℝ}
    (hσ : 0 < σ) :
    (∀ β β' : Fin p → ℝ, (∀ i, obsLaw (logLinearLaw μ₀ (β ⬝ᵥ x i) σ) (μC i) =
        obsLaw (logLinearLaw μ₀ (β' ⬝ᵥ x i) σ) (μC i)) → β = β') ↔
      Function.Injective (Matrix.of x).mulVec := by
  have hdot : ∀ β : Fin p → ℝ, ∀ i, (Matrix.of x).mulVec β i = β ⬝ᵥ x i := fun β i => by
    simp [Matrix.mulVec, dotProduct_comm]
  constructor
  · intro H β β' hββ'
    refine H β β' fun i => ?_
    rw [← hdot, ← hdot, hββ']
  · intro hx β β' H
    refine hx (funext fun i => ?_)
    rw [hdot, hdot]
    exact (eq_of_obsLaw_eq μ₀ hS (μC i) (hC i) hσ hσ (H i)).1

end

end MathlibExt.Probability.Statistics.AFTEstimation
