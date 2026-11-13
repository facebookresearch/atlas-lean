/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.FisherInformation
public import MathlibExt.Probability.Statistics.MLEAsymptoticNormality
public import MathlibExt.Probability.Statistics.MultivariateCLT
public import MathlibExt.Probability.Distributions.CochranTheorem
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.StrongLaw

/-!
# Finite-dimensional Fisher information and regular likelihood inference

The parameter `θ` ranges over a finite-dimensional real inner product space `E` (for example
`EuclideanSpace ℝ (Fin d)`), and `p θ` is a family of densities with respect to a reference
measure `ν`. The **score** is the gradient `∇_θ log p θ x ∈ E` (`score`) and the **Fisher
information** is the operator `I(θ) = E_θ [s sᵀ]` (`fisherInformation`), with quadratic form
`⟪I(θ) u, u⟫ = E_θ ⟪s, u⟫²`. Every result here is the vector form of a one-parameter result in
`FisherInformation`, `MLEAsymptoticNormality` and `LikelihoodRatioTests`:

* Cramér–Rao reduces to the scalar inequality along the line `t ↦ θ + t • u`, whose scalar
  Fisher information is `⟪I(θ) u, u⟫` (`inner_fisherInformation_self`).
* The score CLT is the multivariate CLT (Cramér–Wold reduction to the scalar CLT).
* Asymptotic normality of consistent roots of the likelihood equation follows the scalar Taylor
  argument, with the Hessian average converging by the Banach-valued strong law and the
  nonsingular information inverted as an operator.
* The Wald, score and likelihood-ratio statistics converge to `χ²_d`, `d = dim E`; the
  chi-square law comes from diagonalizing the information in an orthonormal eigenbasis and
  Cochran's theorem (`ProbabilityTheory.stdGaussian_map_sum_sq_inner`).

## Standing assumptions and what is not claimed

* **Interiority.** All asymptotic results assume the regularity conditions on a ball of radius
  `δ > 0` about `θ₀`, so `θ₀` is an interior point. Boundary parameters (where the limit is a
  projected Gaussian, as in the `d = 1` result
  `LikelihoodRatioTests.tendstoInDistribution_two_mul_logLikelihood_max_zero_sub`) are not
  covered.
* **Nonsingular information.** The matrix Cramér–Rao bound, the asymptotic normality of the
  likelihood roots, and the three tests assume `I(θ₀)` nonsingular (`IsUnit`, or positive
  definite, which implies it by `isUnit_of_inner_self_pos`). Singular information is excluded;
  only the directional Cramér–Rao bound and the score CLT allow it.
* **Existence and consistency of estimators are inputs.** The asymptotic theorems take as
  hypotheses that `θhat n` solves the likelihood equation with probability tending to one and
  converges to `θ₀` in probability. Neither is inferred from the score CLT. Consistency of a
  maximizer follows, for a compact parameter space and an **identifiable** model, from Wald's
  theorem `FisherInformation.ae_tendsto_maximumLikelihood`; identifiability enters only there.
* **Moment identities are inputs.** The centering `E score = 0` and the information identity
  `E Dscore = -I(θ₀)` are assumed directly; they are what differentiating `∫ p θ dν = 1` twice
  under the integral sign gives.
* Only a simple null hypothesis `θ = θ₀` is tested; composite nulls with `r` restrictions
  (limit `χ²_r`) are not covered.
* **Null information in the Wald and score statistics.** Both use the null information
  `I(θ₀)`, known under the simple null. Versions with an estimated information (`I(θhat n)` or
  the observed information) and the consistency of the observed information, which the
  one-parameter `LikelihoodRatioTests` provides (`_of_estimator` variants,
  `tendstoInMeasure_observedInformation`), are not covered here.
* **Wilks at the root.** The likelihood-ratio statistic is `2 (ℓₙ(θhat n) - ℓₙ(θ₀))` evaluated
  at the consistent root `θhat n`, not the supremum form `2 (sup_θ ℓₙ θ - ℓₙ θ₀)`.

## Main results

* `inner_fisherInformation_apply`, `inner_fisherInformation_self_nonneg`,
  `inner_fisherInformation_comm`: the bilinear form, positive semidefiniteness, symmetry.
* `inner_fisherInformation_self`: `⟪I(θ) u, u⟫` is the scalar Fisher information of the line
  submodel through `θ` in direction `u`.
* `sq_fderiv_le_inner_fisherInformation_mul`: directional Cramér–Rao,
  `(Dg(θ) u)² ≤ ⟪I(θ) u, u⟫ Var_θ T`.
* `cramerRao`: matrix Cramér–Rao, `⟪∇g, I(θ)⁻¹ ∇g⟫ ≤ Var_θ T` for nonsingular `I(θ)`.
* `tendstoInDistribution_score`: `n^{-1/2} ∑ score p θ₀ (X i) → N(0, I(θ₀))`.
* `tendstoInDistribution_sqrt_smul_sub_of_estimatingEquation`: the multivariate Z-estimator
  theorem, `√n (θhat n - θ₀) → -D⁻¹ N(0, E ψ ψᵀ)`, `D = E Dψ θ₀`.
* `tendstoInDistribution_sqrt_smul_sub_of_likelihoodEquation`:
  `√n (θhat n - θ₀) → N(0, I(θ₀)⁻¹)`.
* `hasLaw_inner_inverse_chiSquare`: `⟪S⁻¹ V, V⟫ ~ χ²_d` for `V ~ N(0, S)`, `S` positive definite.
* `tendstoInDistribution_waldStatistic`, `tendstoInDistribution_scoreStatistic`,
  `tendstoInDistribution_two_mul_logLikelihood_sub`: Wald, Rao and Wilks, each with limit
  `χ²_d`.

## References

* H. Cramér, *Mathematical Methods of Statistics* (1946), ch. 32 and §33.3.
* C. R. Rao, "Information and the accuracy attainable in the estimation of statistical
  parameters", Bull. Calcutta Math. Soc. 37 (1945) 81–91.
* S. S. Wilks, "The large-sample distribution of the likelihood ratio for testing composite
  hypotheses", Ann. Math. Statist. 9 (1938) 60–62.
* A. Wald, "Tests of statistical hypotheses concerning several parameters when the number of
  observations is large", Trans. Amer. Math. Soc. 54 (1943) 426–482.
* C. R. Rao, "Large sample tests of statistical hypotheses concerning several parameters with
  applications to problems of estimation", Proc. Cambridge Philos. Soc. 44 (1948) 50–57.
* E. L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed. (1998), §2.6, §6.5.
* A. W. van der Vaart, *Asymptotic Statistics* (1998), Theorem 5.41 and ch. 16.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.VectorInference

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace
open MathlibExt.Probability.Statistics.FisherInformation (lawOf)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **score vector** `∇_θ log p θ x ∈ E` of a family of densities `p θ` indexed by a
finite-dimensional real inner product space `E`. -/
noncomputable def score (p : E → 𝓧 → ℝ) (θ : E) (x : 𝓧) : E :=
  gradient (fun t => Real.log (p t x)) θ

omit [FiniteDimensional ℝ E] in
private theorem continuous_rankOne_self :
    Continuous fun s : E => InnerProductSpace.rankOne ℝ s s := by
  have e : (fun s : E => InnerProductSpace.rankOne ℝ s s) =
      fun s => ContinuousLinearMap.smulRightL ℝ E E (innerSL ℝ s) s := by
    funext s; ext v; simp
  rw [e]
  exact (ContinuousLinearMap.smulRightL ℝ E E).continuous₂.comp
    ((innerSL ℝ).continuous.prodMk continuous_id)

/-- The **Fisher information operator** of the family `p` at `θ`: the second moment
`E_θ [s sᵀ]` of the score `s = score p θ` under the law `p θ ν` (the Bochner integral of the
rank-one operators `InnerProductSpace.rankOne ℝ s s : v ↦ ⟪s, v⟫ • s`), as a continuous linear
map `E →L[ℝ] E`. Its quadratic form is `⟪I(θ) u, u⟫ = E_θ ⟪s, u⟫²`
(`inner_fisherInformation_apply`). If the score is not square integrable the Bochner integral
takes its junk value `0`. -/
noncomputable def fisherInformation (ν : Measure 𝓧) (p : E → 𝓧 → ℝ) (θ : E) : E →L[ℝ] E :=
  ∫ x, InnerProductSpace.rankOne ℝ (score p θ x) (score p θ x) ∂(lawOf ν p θ)

private theorem inner_integral_rankOne {μ : Measure 𝓧} {s : 𝓧 → E}
    (h : Integrable (fun x => InnerProductSpace.rankOne ℝ (s x) (s x)) μ) (u v : E) :
    ⟪(∫ x, InnerProductSpace.rankOne ℝ (s x) (s x) ∂μ) u, v⟫ =
      ∫ x, ⟪s x, u⟫ * ⟪s x, v⟫ ∂μ := by
  rw [ContinuousLinearMap.integral_apply h, real_inner_comm, ← integral_inner
    (h.apply_continuousLinearMap u)]
  congr 1; funext x
  rw [InnerProductSpace.rankOne_apply, real_inner_smul_right, real_inner_comm (s x) v]

omit [FiniteDimensional ℝ E] in
private theorem integrable_rankOne {μ : Measure 𝓧} {s : 𝓧 → E} (hs : MemLp s 2 μ) :
    Integrable (fun x => InnerProductSpace.rankOne ℝ (s x) (s x)) μ := by
  refine Integrable.mono' (hs.integrable_norm_pow two_ne_zero)
    (continuous_rankOne_self.comp_aestronglyMeasurable hs.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [InnerProductSpace.norm_rankOne, sq]

/-- The bilinear form of the Fisher information: for a square-integrable score,
`⟪I(θ) u, v⟫ = E_θ [⟪s, u⟫ ⟪s, v⟫]`. -/
theorem inner_fisherInformation_apply {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ : E}
    (hs : MemLp (score p θ) 2 (lawOf ν p θ)) (u v : E) :
    ⟪fisherInformation ν p θ u, v⟫ =
      ∫ x, ⟪score p θ x, u⟫ * ⟪score p θ x, v⟫ ∂(lawOf ν p θ) :=
  inner_integral_rankOne (integrable_rankOne hs) u v

/-- The Fisher information is positive semidefinite: `0 ≤ ⟪I(θ) u, u⟫` (unconditionally; the
junk value `0` is also positive semidefinite). -/
theorem inner_fisherInformation_self_nonneg (ν : Measure 𝓧) (p : E → 𝓧 → ℝ) (θ u : E) :
    0 ≤ ⟪fisherInformation ν p θ u, u⟫ := by
  by_cases h : Integrable (fun x => InnerProductSpace.rankOne ℝ (score p θ x) (score p θ x))
    (lawOf ν p θ)
  · rw [fisherInformation, inner_integral_rankOne h]
    exact integral_nonneg fun x => mul_self_nonneg _
  · simp [fisherInformation, integral_undef h]

/-- The Fisher information is symmetric: `⟪I(θ) u, v⟫ = ⟪u, I(θ) v⟫`. -/
theorem inner_fisherInformation_comm (ν : Measure 𝓧) (p : E → 𝓧 → ℝ) (θ u v : E) :
    ⟪fisherInformation ν p θ u, v⟫ = ⟪u, fisherInformation ν p θ v⟫ := by
  by_cases h : Integrable (fun x => InnerProductSpace.rankOne ℝ (score p θ x) (score p θ x))
    (lawOf ν p θ)
  · rw [← real_inner_comm u, fisherInformation, inner_integral_rankOne h, inner_integral_rankOne h]
    simp_rw [mul_comm]
  · simp [fisherInformation, integral_undef h]

/-! ### Reduction to one-parameter submodels -/

omit [FiniteDimensional ℝ E] in
/-- The line `t ↦ θ + t • u` through `θ` in direction `u` has velocity `u`, so the
one-parameter submodel `t ↦ f (θ + t • u)` has derivative `Df(θ) u` at `0`. -/
theorem hasDerivAt_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    {θ : E} (hf : DifferentiableAt ℝ f θ) (u : E) :
    HasDerivAt (fun t : ℝ => f (θ + t • u)) (fderiv ℝ f θ u) 0 := by
  have hl : HasDerivAt (fun t : ℝ => θ + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add θ
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hl (by simp)

omit [FiniteDimensional ℝ E] in
/-- The line `t ↦ θ + t • u` tends to `θ` as `t → 0`. -/
theorem tendsto_line (θ u : E) : Tendsto (fun t : ℝ => θ + t • u) (𝓝 0) (𝓝 θ) := by
  have h : Continuous fun t : ℝ => θ + t • u := by fun_prop
  simpa using h.tendsto 0

omit [MeasurableSpace 𝓧] in
/-- For a positive density differentiable at `θ`, `⟪score p θ x, u⟫ = ∂_u p θ x / p θ x`. -/
theorem inner_score_eq {p : E → 𝓧 → ℝ} {θ : E} {x : 𝓧} (hp_pos : 0 < p θ x)
    (hp_diff : DifferentiableAt ℝ (fun t => p t x) θ) (u : E) :
    ⟪score p θ x, u⟫ = fderiv ℝ (fun t => p t x) θ u / p θ x := by
  rw [score, inner_gradient_left, (hp_diff.hasFDerivAt.log hp_pos.ne').fderiv]
  simp [div_eq_inv_mul]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem integral_lawOf {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ : E}
    (hp_nonneg : ∀ x, 0 ≤ p θ x) (hp_meas : Measurable (p θ)) (g : 𝓧 → ℝ) :
    ∫ x, g x ∂(lawOf ν p θ) = ∫ x, p θ x * g x ∂ν := by
  rw [lawOf, integral_withDensity_eq_integral_toReal_smul hp_meas.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  congr 1; funext x
  rw [ENNReal.toReal_ofReal (hp_nonneg x), smul_eq_mul]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem integrable_lawOf_iff {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ : E}
    (hp_nonneg : ∀ x, 0 ≤ p θ x) (hp_meas : Measurable (p θ)) (g : 𝓧 → ℝ) :
    Integrable g (lawOf ν p θ) ↔ Integrable (fun x => p θ x * g x) ν := by
  rw [lawOf, integrable_withDensity_iff_integrable_smul' hp_meas.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (hp_nonneg x), smul_eq_mul]

/-- **The quadratic form of the Fisher information is a scalar Fisher information.** For a
positive density family differentiable at `θ` with square-integrable score, `⟪I(θ) u, u⟫` is
the one-parameter Fisher information (`FisherInformation.fisherInformation`) at `0` of the
submodel `t ↦ p (θ + t • u)` along the line through `θ` in direction `u`. -/
theorem inner_fisherInformation_self {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ : E}
    (hp_pos : ∀ x, 0 < p θ x) (hp_meas : Measurable (p θ))
    (hp_diff : ∀ x, DifferentiableAt ℝ (fun t => p t x) θ)
    (hs : MemLp (score p θ) 2 (lawOf ν p θ)) (u : E) :
    ⟪fisherInformation ν p θ u, u⟫ =
      FisherInformation.fisherInformation ν (fun t x => p (θ + t • u) x) 0 := by
  rw [inner_fisherInformation_apply hs, integral_lawOf (fun x => (hp_pos x).le) hp_meas,
    FisherInformation.fisherInformation]
  congr 1; funext x
  rw [(hasDerivAt_line (f := fun t => p t x) (hp_diff x) u).deriv,
    inner_score_eq (hp_pos x) (hp_diff x), zero_smul, add_zero]
  have := (hp_pos x).ne'
  field_simp

variable [MeasurableSpace E] [BorelSpace E]

/-- **Cramér–Rao inequality, directional form.** Let `p θ'` be positive probability densities
with respect to `ν` for `θ'` near `θ`, differentiable in the parameter at `θ`, with a
measurable score of finite second moment under `p θ ν`, and let `T` be an estimator with
finite second moment that is unbiased for `g θ'` near `θ`, with `g` differentiable at `θ`. If,
along the line through `θ` in direction `u`, `∫ p dν` and `∫ T p dν` can be differentiated
under the integral sign at `θ`, then `(Dg(θ) u)² ≤ ⟪I(θ) u, u⟫ · Var_θ T`.

The proof applies the one-parameter `FisherInformation.sq_deriv_le_fisherInformation_mul` to the
submodel `t ↦ p (θ + t • u)` and identifies its information by
`inner_fisherInformation_self`.

Source: Rao (1945), Cramér (1946), ch. 32 (several parameters); Lehmann & Casella (1998),
Theorem 2.6.6. -/
theorem sq_fderiv_le_inner_fisherInformation_mul {ν : Measure 𝓧} {p : E → 𝓧 → ℝ}
    {T : 𝓧 → ℝ} {g : E → ℝ} {θ : E} (u : E)
    (hp_pos : ∀ θ' x, 0 < p θ' x) (hp_meas : Measurable (p θ))
    (hp_int : ∀ᶠ θ' in 𝓝 θ, ∫ x, p θ' x ∂ν = 1)
    (hp_diff : ∀ x, DifferentiableAt ℝ (fun t => p t x) θ)
    (hs_meas : Measurable (score p θ))
    (hs_sq : Integrable (fun x => ‖score p θ x‖ ^ 2) (lawOf ν p θ))
    (hT_meas : AEStronglyMeasurable T ν)
    (hT_sq : Integrable (fun x => T x ^ 2 * p θ x) ν)
    (h_unbiased : ∀ᶠ θ' in 𝓝 θ, ∫ x, T x * p θ' x ∂ν = g θ')
    (hg : DifferentiableAt ℝ g θ)
    (h_deriv_one : HasDerivAt (fun t : ℝ => ∫ x, p (θ + t • u) x ∂ν)
      (∫ x, fderiv ℝ (fun t => p t x) θ u ∂ν) 0)
    (h_deriv_T : HasDerivAt (fun t : ℝ => ∫ x, T x * p (θ + t • u) x ∂ν)
      (∫ x, T x * fderiv ℝ (fun t => p t x) θ u ∂ν) 0) :
    fderiv ℝ g θ u ^ 2 ≤ ⟪fisherInformation ν p θ u, u⟫ * ∫ x, (T x - g θ) ^ 2 * p θ x ∂ν := by
  have hs : MemLp (score p θ) 2 (lawOf ν p θ) :=
    (memLp_two_iff_integrable_sq_norm hs_meas.aestronglyMeasurable).2 hs_sq
  set pl : ℝ → 𝓧 → ℝ := fun t x => p (θ + t • u) x with hpl
  have hpl0 : ∀ x, pl 0 x = p θ x := fun x => by simp [hpl]
  have hderiv : ∀ x, deriv (fun t => pl t x) 0 = fderiv ℝ (fun t => p t x) θ u := fun x =>
    (hasDerivAt_line (f := fun t => p t x) (hp_diff x) u).deriv
  have hDp : ∀ x, fderiv ℝ (fun t => p t x) θ u = p θ x * ⟪score p θ x, u⟫ := fun x => by
    rw [inner_score_eq (hp_pos θ x) (hp_diff x)]
    field_simp [(hp_pos θ x).ne']
  have hline := tendsto_line θ u
  have h := FisherInformation.sq_deriv_le_fisherInformation_mul (p := pl)
    (g := fun t => g (θ + t • u)) (T := T) (θ := 0)
    (fun t x => (hp_pos _ x).le) (hline.eventually hp_int)
    (by
      simp_rw [hderiv, hDp]
      exact hp_meas.aestronglyMeasurable.mul
        ((continuous_id.inner continuous_const).comp_aestronglyMeasurable
          hs_meas.aestronglyMeasurable))
    (by
      simp_rw [hderiv, hpl0]
      have hi : Integrable (fun x => ⟪score p θ x, u⟫ ^ 2) (lawOf ν p θ) := by
        refine Integrable.mono' (hs_sq.mul_const (‖u‖ ^ 2))
          (((continuous_id.inner continuous_const).pow 2).comp_aestronglyMeasurable
            hs_meas.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs, abs_pow, ← mul_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
      refine ((integrable_lawOf_iff (fun x => (hp_pos θ x).le) hp_meas _).1 hi).congr
        (Eventually.of_forall fun x => ?_)
      simp only
      rw [hDp]
      field_simp [(hp_pos θ x).ne'])
    hT_meas (by simp_rw [hpl0]; exact hT_sq) (hline.eventually h_unbiased)
    (by simp_rw [hderiv]; exact h_deriv_one) (by simp_rw [hderiv]; exact h_deriv_T)
  rw [(hasDerivAt_line hg u).deriv, ← inner_fisherInformation_self (hp_pos θ) hp_meas hp_diff hs]
    at h
  simpa [hpl0] using h

omit [MeasurableSpace E] [BorelSpace E] in
/-- A positive definite operator on a finite-dimensional space is invertible. -/
theorem isUnit_of_inner_self_pos {A : E →L[ℝ] E} (h : ∀ u, u ≠ 0 → 0 < ⟪A u, u⟫) :
    IsUnit A := by
  have hinj : Function.Injective A := by
    intro a b hab
    by_contra hne
    have := h (a - b) (sub_ne_zero.2 hne)
    rw [map_sub, hab, sub_self, inner_zero_left] at this
    exact lt_irrefl _ this
  let e : E ≃L[ℝ] E :=
    (LinearEquiv.ofInjectiveEndo (A : E →ₗ[ℝ] E) hinj).toContinuousLinearEquiv
  exact ⟨(ContinuousLinearEquiv.unitsEquiv ℝ E).symm e, by ext v; rfl⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `A (A⁻¹ v) = v` for an invertible operator, with `A⁻¹ = Ring.inverse A`. -/
theorem apply_inverse_apply {A : E →L[ℝ] E} (hA : IsUnit A) (v : E) :
    A (Ring.inverse A v) = v := by
  change (A * Ring.inverse A) v = v
  rw [Ring.mul_inverse_cancel A hA]; rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `A⁻¹ (A v) = v` for an invertible operator, with `A⁻¹ = Ring.inverse A`. -/
theorem inverse_apply_apply {A : E →L[ℝ] E} (hA : IsUnit A) (v : E) :
    Ring.inverse A (A v) = v := by
  change (Ring.inverse A * A) v = v
  rw [Ring.inverse_mul_cancel A hA]; rfl

/-- **Cramér–Rao inequality with nonsingular information.** Under the hypotheses of
`sq_fderiv_le_inner_fisherInformation_mul` in every direction, if the Fisher information
`I(θ)` is invertible, then `Var_θ T ≥ ⟪∇g(θ), I(θ)⁻¹ ∇g(θ)⟫`, the matrix form
`∇gᵀ I⁻¹ ∇g ≤ Var T`. Invertibility follows from positive definiteness
(`isUnit_of_inner_self_pos`); for singular information this statement is not claimed, and the
directional form still applies.

Source: Rao (1945), Cramér (1946), ch. 32; Lehmann & Casella (1998), Theorem 2.6.6. -/
theorem cramerRao {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {T : 𝓧 → ℝ} {g : E → ℝ} {θ : E}
    (hp_pos : ∀ θ' x, 0 < p θ' x) (hp_meas : Measurable (p θ))
    (hp_int : ∀ᶠ θ' in 𝓝 θ, ∫ x, p θ' x ∂ν = 1)
    (hp_diff : ∀ x, DifferentiableAt ℝ (fun t => p t x) θ)
    (hs_meas : Measurable (score p θ))
    (hs_sq : Integrable (fun x => ‖score p θ x‖ ^ 2) (lawOf ν p θ))
    (hI : IsUnit (fisherInformation ν p θ))
    (hT_meas : AEStronglyMeasurable T ν)
    (hT_sq : Integrable (fun x => T x ^ 2 * p θ x) ν)
    (h_unbiased : ∀ᶠ θ' in 𝓝 θ, ∫ x, T x * p θ' x ∂ν = g θ')
    (hg : DifferentiableAt ℝ g θ)
    (h_deriv_one : ∀ u : E, HasDerivAt (fun t : ℝ => ∫ x, p (θ + t • u) x ∂ν)
      (∫ x, fderiv ℝ (fun t => p t x) θ u ∂ν) 0)
    (h_deriv_T : ∀ u : E, HasDerivAt (fun t : ℝ => ∫ x, T x * p (θ + t • u) x ∂ν)
      (∫ x, T x * fderiv ℝ (fun t => p t x) θ u ∂ν) 0) :
    ⟪gradient g θ, Ring.inverse (fisherInformation ν p θ) (gradient g θ)⟫ ≤
      ∫ x, (T x - g θ) ^ 2 * p θ x ∂ν := by
  set I := fisherInformation ν p θ
  set u := Ring.inverse I (gradient g θ)
  set c := ⟪gradient g θ, u⟫
  have hIu : I u = gradient g θ := apply_inverse_apply hI _
  have hc : fderiv ℝ g θ u = c := (inner_gradient_left (f := g) (x := θ) (y := u)).symm
  have hcI : ⟪I u, u⟫ = c := by rw [hIu]
  have hc0 : 0 ≤ c := hcI ▸ inner_fisherInformation_self_nonneg ν p θ u
  have h := sq_fderiv_le_inner_fisherInformation_mul u hp_pos hp_meas hp_int hp_diff hs_meas
    hs_sq hT_meas hT_sq h_unbiased hg (h_deriv_one u) (h_deriv_T u)
  rw [hc, hcI] at h
  have hV0 : 0 ≤ ∫ x, (T x - g θ) ^ 2 * p θ x ∂ν :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hp_pos θ x).le
  rcases hc0.eq_or_lt with h0 | hpos
  · rw [← h0]; exact hV0
  · nlinarith

/-! ### Laws determined by projections -/

section Laws

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Ω'' : Type*} [MeasurableSpace Ω''] {P'' : Measure Ω''} [IsProbabilityMeasure P'']

omit [MeasurableSpace E] [BorelSpace E] in
/-- Convergence in distribution only depends on the law of the limit. -/
theorem _root_.MeasureTheory.TendstoInDistribution.of_map_eq {F : Type*} [TopologicalSpace F]
    [MeasurableSpace F] [OpensMeasurableSpace F] {X : ℕ → Ω → F} {Y : Ω' → F} {Z : Ω'' → F}
    (h : TendstoInDistribution X atTop Y (fun _ => P) P') (hZ : AEMeasurable Z P'')
    (hmap : P'.map Y = P''.map Z) : TendstoInDistribution X atTop Z (fun _ => P) P'' where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hZ
  tendsto := by
    have e : (⟨P''.map Z, inferInstance⟩ : ProbabilityMeasure F) =
        ⟨P'.map Y, inferInstance⟩ :=
      Subtype.ext hmap.symm
    rw [e]; exact h.tendsto

omit [IsProbabilityMeasure P] [IsProbabilityMeasure P'] in
/-- Two random vectors whose scalar projections all have the same laws have the same law. -/
theorem map_eq_of_forall_map_inner {Y : Ω → E} {Z : Ω' → E} (hY : AEMeasurable Y P)
    (hZ : AEMeasurable Z P') [IsFiniteMeasure P] [IsFiniteMeasure P']
    (h : ∀ t, P.map (fun ω => ⟪Y ω, t⟫) = P'.map (fun ω => ⟪Z ω, t⟫)) :
    P.map Y = P'.map Z :=
  Measure.ext_of_charFun (funext fun t => by
    rw [charFun_map_eq_charFun_map_inner_one hY, charFun_map_eq_charFun_map_inner_one hZ, h])

end Laws

/-! ### The score statistic -/

section Asymptotics

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- The variance of a projection of the score is the Fisher information quadratic form. -/
theorem variance_inner_score {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ₀ : E}
    {X₀ : Ω → 𝓧} (hX_law : HasLaw X₀ (lawOf ν p θ₀) P)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => ‖score p θ₀ x‖ ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂(lawOf ν p θ₀) = 0) (t : E) :
    Var[fun ω => ⟪score p θ₀ (X₀ ω), t⟫; P] = ⟪fisherInformation ν p θ₀ t, t⟫ := by
  have : IsProbabilityMeasure (lawOf ν p θ₀) := hX_law.isProbabilityMeasure_iff.1 inferInstance
  have hs : MemLp (score p θ₀) 2 (lawOf ν p θ₀) :=
    (memLp_two_iff_integrable_sq_norm hs_meas.aestronglyMeasurable).2 hs_sq
  have hinner : Measurable fun x => ⟪score p θ₀ x, t⟫ :=
    (continuous_id.inner continuous_const).measurable.comp hs_meas
  have hL2 : MemLp (fun ω => ⟪score p θ₀ (X₀ ω), t⟫) 2 P :=
    hX_law.memLp_comp (f := fun x => ⟪score p θ₀ x, t⟫) (hs.inner_const t)
  have hmean : P[fun ω => ⟪score p θ₀ (X₀ ω), t⟫] = 0 := by
    change ∫ ω, ((fun x => ⟪score p θ₀ x, t⟫) ∘ X₀) ω ∂P = 0
    rw [hX_law.integral_comp (f := fun x => ⟪score p θ₀ x, t⟫) hinner.aestronglyMeasurable]
    simp_rw [real_inner_comm t]
    rw [integral_inner (hs.integrable one_le_two), hs_mean, inner_zero_right]
  rw [variance_of_integral_eq_zero hL2.aemeasurable hmean]
  change ∫ ω, ((fun x => ⟪score p θ₀ x, t⟫ ^ 2) ∘ X₀) ω ∂P = _
  rw [hX_law.integral_comp (f := fun x => ⟪score p θ₀ x, t⟫ ^ 2)
      (hinner.pow_const 2).aestronglyMeasurable, inner_fisherInformation_apply hs]
  simp_rw [sq]

/-- **Central limit theorem for the score vector.** For i.i.d. observations with law
`p θ₀ ν`, a measurable score with mean zero and finite second moment, the normalized score
`n^{-1/2} ∑_{i<n} score p θ₀ (X i)` converges in distribution to `N(0, I(θ₀))`: to any random
vector `Y` all of whose projections `⟪Y, t⟫` are `N(0, ⟪I(θ₀) t, t⟫)`. The information may
be singular here.

Source: Lehmann & Casella (1998), §6.5; van der Vaart (1998), ch. 5; obtained from the
multivariate CLT `ProbabilityTheory.tendstoInDistribution_inv_sqrt_smul_sum_sub` (Cramér–Wold
reduction to the scalar CLT). -/
theorem tendstoInDistribution_score {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ₀ : E}
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => ‖score p θ₀ x‖ ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂(lawOf ν p θ₀) = 0)
    {Y : Ω' → E} (hY_meas : AEMeasurable Y P')
    (hY : ∀ t, HasLaw (fun ω => ⟪Y ω, t⟫)
      (gaussianReal 0 (⟪fisherInformation ν p θ₀ t, t⟫).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => (√n)⁻¹ • ∑ i ∈ Finset.range n, score p θ₀ (X i ω))
      atTop Y (fun _ => P) P' := by
  have hs : MemLp (score p θ₀) 2 (lawOf ν p θ₀) :=
    (memLp_two_iff_integrable_sq_norm hs_meas.aestronglyMeasurable).2 hs_sq
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX_law i).aemeasurable
  have hident : ∀ i, IdentDistrib (score p θ₀ ∘ X i) (score p θ₀ ∘ X 0) P P := fun i =>
    (⟨hXm i, hXm 0, (hX_law i).map_eq.trans (hX_law 0).map_eq.symm⟩ :
      IdentDistrib (X i) (X 0) P P).comp hs_meas
  have hL2 : MemLp (score p θ₀ ∘ X 0) 2 P := (hX_law 0).memLp_comp hs
  have h := tendstoInDistribution_inv_sqrt_smul_sum_sub (X := fun i => score p θ₀ ∘ X i)
    hY_meas (fun t => by
      rw [show (fun ω => ⟪(score p θ₀ ∘ X 0) ω, t⟫) = fun ω => ⟪score p θ₀ (X 0 ω), t⟫ from rfl,
        variance_inner_score (hX_law 0) hs_meas hs_sq hs_mean t]
      exact hY t)
    hL2 (hX_indep.comp (fun _ => score p θ₀) fun _ => hs_meas) hident
  have hmean : ∫ ω, score p θ₀ (X 0 ω) ∂P = 0 := by
    change ∫ ω, (score p θ₀ ∘ X 0) ω ∂P = 0
    rw [(hX_law 0).integral_comp hs_meas.aestronglyMeasurable, hs_mean]
  simpa [hmean] using h

end Asymptotics

/-! ### Asymptotic normality of consistent roots of vector estimating equations -/

section ZEstimator

omit [MeasurableSpace 𝓧] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- **First-order Taylor bound** from a Lipschitz derivative: if `Df` is differentiable on the
ball of radius `δ` about `θ₀` with `‖Df(θ) - Df(θ₀)‖ ≤ C ‖θ - θ₀‖` there, then
`‖f θ - f θ₀ - Df(θ₀) (θ - θ₀)‖ ≤ C ‖θ - θ₀‖²` on the ball. -/
theorem norm_sub_sub_fderiv_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {θ₀ : E} {δ C : ℝ}
    (hf : ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ f θ)
    (hC : ∀ θ ∈ Metric.ball θ₀ δ, ‖fderiv ℝ f θ - fderiv ℝ f θ₀‖ ≤ C * ‖θ - θ₀‖)
    {θ : E} (hθ : θ ∈ Metric.ball θ₀ δ) :
    ‖f θ - f θ₀ - fderiv ℝ f θ₀ (θ - θ₀)‖ ≤ C * ‖θ - θ₀‖ ^ 2 := by
  set r := ‖θ - θ₀‖ with hr
  rcases (norm_nonneg (θ - θ₀)).eq_or_lt with h0 | hpos
  · have : θ = θ₀ := sub_eq_zero.1 (norm_eq_zero.1 h0.symm)
    subst this; simp [hr]
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC θ hθ)
    exact nonneg_of_mul_nonneg_left this (by rw [← hr]; exact hpos)
  have hrδ : r < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hθ
  have hsub : Metric.closedBall θ₀ r ⊆ Metric.ball θ₀ δ := Metric.closedBall_subset_ball hrδ
  set g : E → F := fun y => f y - fderiv ℝ f θ₀ y with hg_def
  have hg : ∀ y ∈ Metric.closedBall θ₀ r, HasFDerivWithinAt g (fderiv ℝ f y - fderiv ℝ f θ₀)
      (Metric.closedBall θ₀ r) y := fun y hy =>
    ((hf y (hsub hy)).hasFDerivAt.sub (fderiv ℝ f θ₀).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ y ∈ Metric.closedBall θ₀ r, ‖fderiv ℝ f y - fderiv ℝ f θ₀‖ ≤ C * r :=
    fun y hy => by
      refine (hC y (hsub hy)).trans (mul_le_mul_of_nonneg_left ?_ hC0)
      rw [Metric.mem_closedBall, dist_eq_norm] at hy; exact hy
  have hθr : θ ∈ Metric.closedBall θ₀ r := by rw [Metric.mem_closedBall, dist_eq_norm]
  have h := (convex_closedBall θ₀ r).norm_image_sub_le_of_norm_hasFDerivWithin_le hg hbound
    (Metric.mem_closedBall_self (norm_nonneg _)) hθr
  have e : g θ - g θ₀ = f θ - f θ₀ - fderiv ℝ f θ₀ (θ - θ₀) := by
    simp only [hg_def, map_sub]; abel
  rw [e] at h
  calc _ ≤ C * r * ‖θ - θ₀‖ := h
    _ = C * ‖θ - θ₀‖ ^ 2 := by rw [hr]; ring

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSpace 𝓧] in
/-- The deterministic core of the Z-estimator argument: if `‖A + B T‖ ≤ r ‖T‖`, `B` is
`η`-close to an operator `D` with left inverse `K`, and `η` is small compared to `‖K‖`, then
`T` is within `2 κ² ‖A‖ η` of `-K A`. -/
private theorem norm_add_inverse_le {D K B : E →L[ℝ] E} {A T : E} {r η κ : ℝ}
    (hK : ∀ v, K (D v) = v) (hκ : ‖K‖ ≤ κ) (hκ0 : 0 < κ)
    (hr : 0 ≤ r) (hAT : ‖A + B T‖ ≤ r * ‖T‖) (hη : ‖B - D‖ + r ≤ η) (hsmall : η ≤ 1 / (2 * κ)) :
    ‖T + K A‖ ≤ 2 * κ ^ 2 * ‖A‖ * η := by
  have hT0 := norm_nonneg T
  have hADT : ‖A + D T‖ ≤ η * ‖T‖ := by
    have e : A + D T = (A + B T) - (B - D) T := by
      simp only [sub_apply]; abel
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have := (B - D).le_opNorm T
    nlinarith
  have hKv : ∀ v, ‖K v‖ ≤ κ * ‖v‖ := fun v =>
    (K.le_opNorm v).trans (mul_le_mul_of_nonneg_right hκ (norm_nonneg v))
  have hηκ : κ * η ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * κ)] at hsmall
    linarith
  have hTle : ‖T‖ ≤ 2 * κ * ‖A‖ := by
    have h1 : ‖T‖ ≤ κ * ‖D T‖ := by have := hKv (D T); rwa [hK] at this
    have h2 : ‖D T‖ ≤ ‖A + D T‖ + ‖A‖ := by
      have := norm_sub_le (A + D T) A
      simpa using this
    nlinarith [norm_nonneg A, norm_nonneg (D T)]
  have e : T + K A = K (A + D T) := by rw [map_add, hK, add_comm]
  rw [e]
  have h3 := hKv (A + D T)
  have hη0 : 0 ≤ η := le_trans (add_nonneg (norm_nonneg _) hr) hη
  calc ‖K (A + D T)‖ ≤ κ * ‖A + D T‖ := h3
    _ ≤ κ * (η * ‖T‖) := mul_le_mul_of_nonneg_left hADT hκ0.le
    _ ≤ κ * (η * (2 * κ * ‖A‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTle hη0) hκ0.le
    _ = 2 * κ ^ 2 * ‖A‖ * η := by ring


omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSpace 𝓧] in
/-- The summed first-order Taylor bound at a root `θ` in the ball:
`‖∑ ψ θ₀ (xᵢ) + (∑ Dψ θ₀ (xᵢ)) (θ - θ₀)‖ ≤ (∑ M (xᵢ)) ‖θ - θ₀‖²`. -/
private theorem norm_sum_add_sum_apply_le {ψ : E → 𝓧 → E} {θ₀ : E} {δ : ℝ}
    (hψ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => ψ t x) θ)
    {M : 𝓧 → ℝ}
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => ψ t x) θ - fderiv ℝ (fun t => ψ t x) θ₀‖ ≤ M x * ‖θ - θ₀‖)
    (n : ℕ) (xs : ℕ → 𝓧) {θ : E} (hθ : θ ∈ Metric.ball θ₀ δ)
    (hroot : ∑ i ∈ Finset.range n, ψ θ (xs i) = 0) :
    ‖∑ i ∈ Finset.range n, ψ θ₀ (xs i) +
        (∑ i ∈ Finset.range n, fderiv ℝ (fun t => ψ t (xs i)) θ₀) (θ - θ₀)‖ ≤
      (∑ i ∈ Finset.range n, M (xs i)) * ‖θ - θ₀‖ ^ 2 := by
  have e : ∑ i ∈ Finset.range n, ψ θ₀ (xs i) +
      (∑ i ∈ Finset.range n, fderiv ℝ (fun t => ψ t (xs i)) θ₀) (θ - θ₀) =
      -∑ i ∈ Finset.range n, (ψ θ (xs i) - ψ θ₀ (xs i) -
        fderiv ℝ (fun t => ψ t (xs i)) θ₀ (θ - θ₀)) := by
    rw [sum_apply, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hroot]
    abel
  rw [e, norm_neg, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact norm_sub_sub_fderiv_le (f := fun t => ψ t (xs i)) (hψ_diff (xs i)) (hM (xs i)) hθ

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSpace 𝓧] in
/-- The summed Taylor bound on the event that `θ` is a root in the ball: with
`A = n^{-1/2} ∑ ψ θ₀ (xᵢ)`, `B = n⁻¹ ∑ Dψ θ₀ (xᵢ)` and `T = √n (θ - θ₀)`,
`‖A + B T‖ ≤ ‖θ - θ₀‖ (n⁻¹ ∑ M (xᵢ)) ‖T‖`. -/
private theorem norm_avg_add_avg_apply_le {ψ : E → 𝓧 → E} {θ₀ : E} {δ : ℝ}
    (hψ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => ψ t x) θ)
    {M : 𝓧 → ℝ}
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => ψ t x) θ - fderiv ℝ (fun t => ψ t x) θ₀‖ ≤ M x * ‖θ - θ₀‖)
    {n : ℕ} (hn : 0 < n) (xs : ℕ → 𝓧) {θ : E} (hθ : θ ∈ Metric.ball θ₀ δ)
    (hroot : ∑ i ∈ Finset.range n, ψ θ (xs i) = 0) :
    ‖(√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, ψ θ₀ (xs i) +
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, fderiv ℝ (fun t => ψ t (xs i)) θ₀)
          (√(n : ℝ) • (θ - θ₀))‖ ≤
      (‖θ - θ₀‖ * ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, M (xs i))) * ‖√(n : ℝ) • (θ - θ₀)‖ := by
  set d := θ - θ₀ with hd
  set H : 𝓧 → E →L[ℝ] E := fun x => fderiv ℝ (fun t => ψ t x) θ₀
  have htay : ‖∑ i ∈ Finset.range n, ψ θ₀ (xs i) + (∑ i ∈ Finset.range n, H (xs i)) d‖
      ≤ (∑ i ∈ Finset.range n, M (xs i)) * ‖d‖ ^ 2 :=
    norm_sum_add_sum_apply_le hψ_diff hM n xs hθ hroot
  have hr : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hrr : (n : ℝ)⁻¹ * √(n : ℝ) = (√(n : ℝ))⁻¹ := by
    have hs : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
    nth_rewrite 1 [← hs]
    rw [mul_inv, mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]
  have e1 : (√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, ψ θ₀ (xs i) +
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, H (xs i)) (√(n : ℝ) • d) =
      (√(n : ℝ))⁻¹ • (∑ i ∈ Finset.range n, ψ θ₀ (xs i) + (∑ i ∈ Finset.range n, H (xs i)) d) := by
    simp only [smul_apply, map_smul, smul_smul, smul_add]
    rw [mul_comm (√(n : ℝ)), hrr]
  change ‖(√(n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, ψ θ₀ (xs i) +
      ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, H (xs i)) (√(n : ℝ) • d)‖ ≤ _
  rw [e1, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
  have e2 : (‖d‖ * ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, M (xs i))) * ‖√(n : ℝ) • d‖ =
      (√(n : ℝ))⁻¹ * ((∑ i ∈ Finset.range n, M (xs i)) * ‖d‖ ^ 2) := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr, smul_eq_mul]
    rw [← hrr]; ring
  rw [e2]
  exact mul_le_mul_of_nonneg_left htay (inv_nonneg.2 hr.le)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [IsProbabilityMeasure P] in
/-- The strong law of large numbers for a Banach-valued transform `g ∘ X i` of an i.i.d.
sequence; only strong measurability of `g` is needed (the Borel structure on the target is
chosen inside the proof). -/
theorem ae_tendsto_average {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [SecondCountableTopology F] {μX : Measure 𝓧} {X : ℕ → Ω → 𝓧}
    (hX_law : ∀ i, HasLaw (X i) μX P) (hX_indep : iIndepFun X P)
    {g : 𝓧 → F} (hg : StronglyMeasurable g) (hgi : Integrable g μX) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, g (X i ω)) atTop
      (𝓝 (∫ x, g x ∂μX)) := by
  let _ : MeasurableSpace F := borel F
  have _ : BorelSpace F := ⟨rfl⟩
  have hgm : Measurable g := hg.measurable
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX_law i).aemeasurable
  have hident : ∀ i, IdentDistrib (g ∘ X i) (g ∘ X 0) P P := fun i =>
    (⟨hXm i, hXm 0, (hX_law i).map_eq.trans (hX_law 0).map_eq.symm⟩ :
      IdentDistrib (X i) (X 0) P P).comp hgm
  have h := strong_law_ae (fun i => g ∘ X i) ((hX_law 0).integrable_comp hgi)
    (fun i j hij => (hX_indep.comp (fun _ => g) fun _ => hgm).indepFun hij) hident
  have e : ∫ ω, g (X 0 ω) ∂P = ∫ x, g x ∂μX :=
    (hX_law 0).integral_comp hgm.aestronglyMeasurable
  simpa only [Function.comp_apply, e] using h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [IsProbabilityMeasure P] in
private theorem tendstoInMeasure_add_zero' {U V : ℕ → Ω → ℝ}
    (hU : TendstoInMeasure P U atTop 0) (hV : TendstoInMeasure P V atTop 0) :
    TendstoInMeasure P (fun i ω => U i ω + V i ω) atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hU hV ⊢
  intro ε hε
  have h2 := (hU (ε / 2) (by positivity)).add (hV (ε / 2) (by positivity))
  rw [add_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => zero_le)
    fun i => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω ⊢
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at h
  linarith [abs_add_le (U i ω) (V i ω)]

/-- The central limit theorem for a mean-zero square-integrable transform `g ∘ X i` of an
i.i.d. sequence, with the limit given by the laws of its projections. -/
theorem tendstoInDistribution_inv_sqrt_smul_sum_comp {μX : Measure 𝓧} {X : ℕ → Ω → 𝓧}
    (hX_law : ∀ i, HasLaw (X i) μX P) (hX_indep : iIndepFun X P)
    {g : 𝓧 → E} (hg : Measurable g) (hg_sq : Integrable (fun x => ‖g x‖ ^ 2) μX)
    (hg_mean : ∫ x, g x ∂μX = 0) {Y : Ω' → E} (hY_meas : AEMeasurable Y P')
    (hY : ∀ t, HasLaw (fun ω => ⟪Y ω, t⟫) (gaussianReal 0 (∫ x, ⟪g x, t⟫ ^ 2 ∂μX).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => (√n)⁻¹ • ∑ i ∈ Finset.range n, g (X i ω))
      atTop Y (fun _ => P) P' := by
  have : IsProbabilityMeasure μX := (hX_law 0).isProbabilityMeasure_iff.1 inferInstance
  have hs : MemLp g 2 μX := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2 hg_sq
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX_law i).aemeasurable
  have hident : ∀ i, IdentDistrib (g ∘ X i) (g ∘ X 0) P P := fun i =>
    (⟨hXm i, hXm 0, (hX_law i).map_eq.trans (hX_law 0).map_eq.symm⟩ :
      IdentDistrib (X i) (X 0) P P).comp hg
  have hL2 : MemLp (g ∘ X 0) 2 P := (hX_law 0).memLp_comp hs
  have hvar : ∀ t, Var[fun ω => ⟪(g ∘ X 0) ω, t⟫; P] = ∫ x, ⟪g x, t⟫ ^ 2 ∂μX := fun t => by
    have hinner : Measurable fun x => ⟪g x, t⟫ :=
      (continuous_id.inner continuous_const).measurable.comp hg
    have hL2' : MemLp (fun ω => ⟪g (X 0 ω), t⟫) 2 P :=
      (hX_law 0).memLp_comp (f := fun x => ⟪g x, t⟫) (hs.inner_const t)
    have hmean : P[fun ω => ⟪g (X 0 ω), t⟫] = 0 := by
      change ∫ ω, ((fun x => ⟪g x, t⟫) ∘ X 0) ω ∂P = 0
      rw [(hX_law 0).integral_comp (f := fun x => ⟪g x, t⟫) hinner.aestronglyMeasurable]
      simp_rw [real_inner_comm t]
      rw [integral_inner (hs.integrable one_le_two), hg_mean, inner_zero_right]
    change Var[fun ω => ⟪g (X 0 ω), t⟫; P] = _
    rw [variance_of_integral_eq_zero hL2'.aemeasurable hmean]
    change ∫ ω, ((fun x => ⟪g x, t⟫ ^ 2) ∘ X 0) ω ∂P = _
    rw [(hX_law 0).integral_comp (f := fun x => ⟪g x, t⟫ ^ 2)
      (hinner.pow_const 2).aestronglyMeasurable]
  have h := tendstoInDistribution_inv_sqrt_smul_sum_sub (X := fun i => g ∘ X i)
    hY_meas (fun t => by rw [hvar t]; exact hY t)
    hL2 (hX_indep.comp (fun _ => g) fun _ => hg) hident
  have hmean : ∫ ω, g (X 0 ω) ∂P = 0 := by
    change ∫ ω, (g ∘ X 0) ω ∂P = 0
    rw [(hX_law 0).integral_comp hg.aestronglyMeasurable, hg_mean]
  simpa [hmean] using h

/-- **Asymptotic normality of consistent roots of a vector estimating equation** (multivariate
Z-estimator, Cramér's conditions). Let `X 0, X 1, …` be i.i.d. with law `μX` and let
`ψ : E → 𝓧 → E` be an estimating function with `E ψ θ₀ (X 0) = 0` and finite second moment.
Assume that on the ball of radius `δ > 0` about `θ₀`, `θ ↦ ψ θ x` is differentiable for every
`x` with derivative `Dψ θ x` satisfying the Lipschitz envelope
`‖Dψ θ x - Dψ θ₀ x‖ ≤ M x ‖θ - θ₀‖` for an integrable `M`; that `Dψ θ₀` is strongly measurable
and integrable; and that `D := E Dψ θ₀ (X 0)` is **nonsingular** (`IsUnit D`). Let `θhat n`
solve the estimating equation `∑_{i<n} ψ θ (X i) = 0` with probability tending to one and
converge to `θ₀` in probability; consistency and the existence of roots are hypotheses, not
consequences. Then `√n (θhat n - θ₀) → -D⁻¹ Y` in distribution, where `Y ~ N(0, E ψ ψᵀ)` is
given through the laws of its projections `⟪Y, t⟫ ~ N(0, E ⟪ψ θ₀, t⟫²)`.

`θ₀` must be an interior point (the ball of radius `δ` lies in the parameter domain of `ψ`);
boundary parameters are not covered.

Source: van der Vaart (1998), Theorem 5.41; Lehmann & Casella (1998), Theorem 6.5.1;
multivariate form of
`MLEAsymptoticNormality.tendstoInDistribution_sqrt_mul_sub_of_estimatingEquation`. -/
theorem tendstoInDistribution_sqrt_smul_sub_of_estimatingEquation
    {μX : Measure 𝓧} {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) μX P)
    (hX_indep : iIndepFun X P)
    {ψ : E → 𝓧 → E} {θ₀ : E} {δ : ℝ} (hδ : 0 < δ)
    (hψ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => ψ t x) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M μX)
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => ψ t x) θ - fderiv ℝ (fun t => ψ t x) θ₀‖ ≤ M x * ‖θ - θ₀‖)
    (hψ_meas : Measurable (ψ θ₀)) (hψ_sq : Integrable (fun x => ‖ψ θ₀ x‖ ^ 2) μX)
    (hψ_mean : ∫ x, ψ θ₀ x ∂μX = 0)
    (hψ'_meas : StronglyMeasurable fun x => fderiv ℝ (fun t => ψ t x) θ₀)
    (hψ'_int : Integrable (fun x => fderiv ℝ (fun t => ψ t x) θ₀) μX)
    (hD : IsUnit (∫ x, fderiv ℝ (fun t => ψ t x) θ₀ ∂μX))
    {θhat : ℕ → Ω → E} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, ψ (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Y : Ω' → E} (hY_meas : AEMeasurable Y P')
    (hY : ∀ t, HasLaw (fun ω => ⟪Y ω, t⟫)
      (gaussianReal 0 (∫ x, ⟪ψ θ₀ x, t⟫ ^ 2 ∂μX).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √n • (θhat n ω - θ₀)) atTop
      (fun ω => -Ring.inverse (∫ x, fderiv ℝ (fun t => ψ t x) θ₀ ∂μX) (Y ω))
      (fun _ => P) P' := by
  have : IsProbabilityMeasure μX := (hX_law 0).isProbabilityMeasure_iff.1 inferInstance
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX_law i).aemeasurable
  set H : 𝓧 → E →L[ℝ] E := fun x => fderiv ℝ (fun t => ψ t x) θ₀ with hH_def
  set D : E →L[ℝ] E := ∫ x, H x ∂μX with hD_def
  set K : E →L[ℝ] E := Ring.inverse D with hK_def
  have hKD : ∀ v, K (D v) = v := inverse_apply_apply hD
  set κ : ℝ := ‖K‖ + 1 with hκ_def
  have hκ0 : 0 < κ := by positivity
  set M' : 𝓧 → ℝ := fun x => |M x| with hM'_def
  have hM'_meas : Measurable M' := continuous_abs.measurable.comp hM_meas
  have hM'_int : Integrable M' μX := hM_int.abs
  have hM'0 : ∀ x, 0 ≤ M' x := fun x => abs_nonneg _
  have hM' : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => ψ t x) θ - fderiv ℝ (fun t => ψ t x) θ₀‖ ≤ M' x * ‖θ - θ₀‖ :=
    fun x θ hθ => (hM x θ hθ).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  set A : ℕ → Ω → E := fun n ω => (√n)⁻¹ • ∑ i ∈ Finset.range n, ψ θ₀ (X i ω) with hA_def
  set B : ℕ → Ω → E →L[ℝ] E := fun n ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, H (X i ω)
    with hB_def
  set Mb : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, M' (X i ω) with hMb_def
  set T : ℕ → Ω → E := fun n ω => √n • (θhat n ω - θ₀) with hT_def
  set η : ℕ → Ω → ℝ := fun n ω => ‖B n ω - D‖ + ‖θhat n ω - θ₀‖ * Mb n ω with hη_def
  -- measurability
  have hB_sm : ∀ n, AEStronglyMeasurable (B n) P := fun n => by
    have h : AEStronglyMeasurable (fun ω => ∑ i ∈ Finset.range n, H (X i ω)) P :=
      Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        hψ'_meas.aestronglyMeasurable.comp_aemeasurable (hXm i)
    exact h.const_smul ((n : ℝ)⁻¹)
  have hMb_meas : ∀ n, AEMeasurable (Mb n) P := fun n => by
    have h : AEMeasurable (fun ω => ∑ i ∈ Finset.range n, M' (X i ω)) P :=
      Finset.aemeasurable_fun_sum _ fun i _ => hM'_meas.comp_aemeasurable (hXm i)
    exact h.const_mul ((n : ℝ)⁻¹)
  have hT_meas : ∀ n, AEMeasurable (T n) P := fun n => ((hθ_meas n).sub_const _).const_smul _
  have hη_meas : ∀ n, AEMeasurable (η n) P := fun n =>
    ((hB_sm n).sub aestronglyMeasurable_const).norm.aemeasurable.add
      (((hθ_meas n).sub_const _).norm.mul (hMb_meas n))
  -- central limit theorem and laws of large numbers
  have hA : TendstoInDistribution A atTop Y (fun _ => P) P' :=
    tendstoInDistribution_inv_sqrt_smul_sum_comp hX_law hX_indep hψ_meas hψ_sq hψ_mean hY_meas hY
  have hB : TendstoInMeasure P B atTop (fun _ => D) :=
    tendstoInMeasure_of_tendsto_ae hB_sm (ae_tendsto_average hX_law hX_indep hψ'_meas hψ'_int)
  have hMb : TendstoInMeasure P Mb atTop (fun _ => ∫ x, M' x ∂μX) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hMb_meas n).aestronglyMeasurable)
      (ae_tendsto_average hX_law hX_indep hM'_meas.stronglyMeasurable hM'_int)
  have hBD : TendstoInMeasure P (fun n ω => ‖B n ω - D‖) atTop 0 := by
    rw [tendstoInMeasure_iff_norm] at hB ⊢
    simpa using hB
  have hdθ : TendstoInMeasure P (fun n ω => ‖θhat n ω - θ₀‖) atTop 0 := by
    rw [tendstoInMeasure_iff_norm] at hcons ⊢
    simpa using hcons
  have hrem : TendstoInMeasure P (fun n ω => ‖θhat n ω - θ₀‖ * Mb n ω) atTop 0 := by
    have h := (hMb.tendstoInDistribution_of_aemeasurable hMb_meas aemeasurable_const
      ).mul_tendstoInMeasure_zero hdθ (fun n => ((hθ_meas n).sub_const _).norm)
    simpa only [mul_comm] using h
  have hη : TendstoInMeasure P η atTop 0 := tendstoInMeasure_add_zero' hBD hrem
  -- the good events
  set G : ℕ → Set Ω := fun n => {ω | ∑ i ∈ Finset.range n, ψ (θhat n ω) (X i ω) = 0} ∩
    {ω | ‖θhat n ω - θ₀‖ < δ} ∩ {ω | η n ω ≤ 1 / (2 * κ)} with hG_def
  have hG : Tendsto (fun n => P (G n)ᶜ) atTop (𝓝 0) := by
    have h1 := (tendstoInMeasure_iff_dist.1 hcons) δ hδ
    have h2 := (tendstoInMeasure_iff_norm.1 hη) (1 / (2 * κ)) (by positivity)
    have h3 := (hroot.add h1).add h2
    simp only [add_zero] at h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => zero_le)
      fun n => ?_
    refine (measure_mono fun ω hω => ?_).trans
      ((measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _))
    simp only [hG_def, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, not_and_or,
      not_lt, not_le] at hω
    simp only [Set.mem_union, Set.mem_ofPred_eq, dist_eq_norm, Pi.zero_apply, sub_zero,
      Real.norm_eq_abs]
    rcases hω with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (h.le.trans (le_abs_self _))
  -- the deterministic bound on the good events
  have hbound : ∀ n, ∀ ω ∈ G n, |‖T n ω + K (A n ω)‖| ≤ 2 * κ ^ 2 * ‖A n ω‖ * η n ω := by
    intro n ω hω
    rw [abs_of_nonneg (norm_nonneg _)]
    obtain ⟨⟨hroot', hclose⟩, hsmall⟩ := hω
    simp only [Set.mem_ofPred_eq] at hroot' hclose hsmall
    set d := θhat n ω - θ₀ with hd
    have hball : θhat n ω ∈ Metric.ball θ₀ δ := by
      rw [Metric.mem_ball, dist_eq_norm]; exact hclose
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hT_def, hA_def]
    have hMb0 : 0 ≤ Mb n ω :=
      smul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n)) (Finset.sum_nonneg fun i _ => hM'0 _)
    have hAT : ‖A n ω + B n ω (T n ω)‖ ≤ (‖d‖ * Mb n ω) * ‖T n ω‖ :=
      norm_avg_add_avg_apply_le hψ_diff hM' hn (fun i => X i ω) hball hroot'
    exact norm_add_inverse_le hKD (by rw [hκ_def]; linarith) hκ0
      (mul_nonneg (norm_nonneg _) hMb0) hAT le_rfl hsmall
  -- `2 κ² ‖A‖ η → 0` in probability
  have hV : TendstoInMeasure P (fun n ω => 2 * κ ^ 2 * ‖A n ω‖ * η n ω) atTop 0 := by
    have hA' := hA.continuous_comp (g := fun x => 2 * κ ^ 2 * ‖x‖) (by fun_prop)
    exact hA'.mul_tendstoInMeasure_zero hη hη_meas
  have hdiff : TendstoInMeasure P (fun n ω => ‖T n ω + K (A n ω)‖) atTop 0 :=
    tendstoInMeasure_zero_of_abs_le hV hG hbound
  have hdiff' : TendstoInMeasure P (T - fun n ω => -K (A n ω)) atTop 0 := by
    rw [tendstoInMeasure_iff_norm] at hdiff ⊢
    simpa using hdiff
  have hlim : TendstoInDistribution (fun n ω => -K (A n ω)) atTop (fun ω => -K (Y ω))
      (fun _ => P) P' := hA.continuous_comp (g := fun v => -K v) (by fun_prop)
  exact tendstoInDistribution_of_tendstoInMeasure_sub T _ hlim hdiff' hT_meas

end ZEstimator

/-! ### The chi-square limit of Gaussian quadratic forms -/

section ChiSquare

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
private theorem inner_sum_smul_sum_smul {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (f g : ι → ℝ) : ⟪∑ i, f i • b i, ∑ i, g i • b i⟫ = ∑ i, f i * g i := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, b.orthonormal.inner_right_fintype]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
private theorem inner_sum_smul {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (f : ι → ℝ) (v : E) : ⟪∑ i, f i • b i, v⟫ = ∑ i, f i * ⟪b i, v⟫ := by
  rw [sum_inner]
  exact Finset.sum_congr rfl fun i _ => real_inner_smul_left _ _ _

/-- Under the standard Gaussian measure, `⟪z, t⟫ ~ N(0, ‖t‖²)`. -/
theorem map_inner_stdGaussian (t : E) :
    (stdGaussian E).map (fun z => ⟪z, t⟫) = gaussianReal 0 (‖t‖ ^ 2).toNNReal := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ t)
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm] at h
  convert h using 2
  funext z
  simp [real_inner_comm]

/-- **Gaussian quadratic forms are chi-square.** Let `S` be a symmetric positive definite
operator on a finite-dimensional real inner product space `E` of dimension `d ≥ 1`, and let
`V ~ N(0, S)`, i.e. `⟪V, t⟫ ~ N(0, ⟪S t, t⟫)` for every `t`. Then
`⟪S⁻¹ V, V⟫ ~ χ²_d`.

The proof diagonalizes `S` in an orthonormal eigenbasis (`LinearMap.IsSymmetric.eigenvectorBasis`),
whitens `V` to a standard Gaussian vector `W`, and applies
`ProbabilityTheory.stdGaussian_map_sum_sq_inner`. -/
theorem hasLaw_inner_inverse_chiSquare {S : E →L[ℝ] E}
    (hS_symm : ∀ u v, ⟪S u, v⟫ = ⟪u, S v⟫) (hS_pos : ∀ u, u ≠ 0 → 0 < ⟪S u, u⟫)
    (hd : 0 < Module.finrank ℝ E) {V : Ω → E} (hV_meas : AEMeasurable V P)
    (hV : ∀ t, HasLaw (fun ω => ⟪V ω, t⟫) (gaussianReal 0 (⟪S t, t⟫).toNNReal) P) :
    HasLaw (fun ω => ⟪Ring.inverse S (V ω), V ω⟫) (chiSquareMeasure (Module.finrank ℝ E)) P := by
  have hsym : (S : E →ₗ[ℝ] E).IsSymmetric := fun u v => hS_symm u v
  set n := Module.finrank ℝ E
  set b := hsym.eigenvectorBasis (rfl : Module.finrank ℝ E = n)
  set lam := hsym.eigenvalues (rfl : Module.finrank ℝ E = n)
  have hSb : ∀ i, S (b i) = lam i • b i := fun i => by
    exact hsym.apply_eigenvectorBasis (rfl : Module.finrank ℝ E = n) i
  have hlam : ∀ i, 0 < lam i := fun i => by
    have h := hS_pos (b i) (b.orthonormal.ne_zero i)
    rwa [hSb, real_inner_smul_left, real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow,
      mul_one] at h
  have hU : IsUnit S := isUnit_of_inner_self_pos hS_pos
  set c : Fin n → ℝ := fun i => (√(lam i))⁻¹ with hc
  have hc2' : ∀ i, c i ^ 2 = (lam i)⁻¹ := fun i => by
    simp only [hc, inv_pow, Real.sq_sqrt (hlam i).le]
  have hc2 : ∀ i, c i ^ 2 * lam i = 1 := fun i => by
    rw [hc2']; exact inv_mul_cancel₀ (hlam i).ne'
  -- whitening
  set W : Ω → E := fun ω => ∑ i, (c i * ⟪b i, V ω⟫) • b i with hW
  set r : E → E := fun t => ∑ i, (c i * ⟪b i, t⟫) • b i with hr
  have hWt : ∀ ω t, ⟪W ω, t⟫ = ⟪V ω, r t⟫ := fun ω t => by
    rw [hW, inner_sum_smul, hr, real_inner_comm, inner_sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hSr : ∀ t, ⟪S (r t), r t⟫ = ‖t‖ ^ 2 := fun t => by
    have e : S (r t) = ∑ i, (c i * ⟪b i, t⟫ * lam i) • b i := by
      simp only [hr, map_sum, map_smul, hSb, smul_smul]
    rw [e, hr, inner_sum_smul_sum_smul, ← b.sum_sq_inner_right t]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hc2 i
    linear_combination ⟪b i, t⟫ ^ 2 * this
  have hW_meas : AEMeasurable W P := by
    refine Finset.aemeasurable_fun_sum _ fun i _ => ?_
    exact ((((continuous_const.inner continuous_id).measurable.comp_aemeasurable hV_meas)
      ).const_mul _).smul_const _
  have hWlaw : P.map W = stdGaussian E := by
    have h := map_eq_of_forall_map_inner (P' := stdGaussian E) (Z := id) hW_meas
      aemeasurable_id fun t => by
        rw [show (fun ω => ⟪W ω, t⟫) = fun ω => ⟪V ω, r t⟫ from funext fun ω => hWt ω t,
          (hV (r t)).map_eq, hSr]
        exact (map_inner_stdGaussian t).symm
    simpa using h
  -- the quadratic form in the whitened coordinates
  have hstat : ∀ ω, ⟪Ring.inverse S (V ω), V ω⟫ = ∑ i, ⟪b i, W ω⟫ ^ 2 := fun ω => by
    set u := ∑ i, ((lam i)⁻¹ * ⟪b i, V ω⟫) • b i
    have hSu : S u = V ω := by
      simp only [u, map_sum, map_smul, hSb, smul_smul]
      conv_rhs => rw [← b.sum_repr' (V ω)]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      field_simp [(hlam i).ne']
    rw [← hSu, inverse_apply_apply hU, hSu, inner_sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hW, b.orthonormal.inner_right_fintype, mul_pow, hc2']
    ring
  refine ⟨?_, ?_⟩
  · exact (Finset.measurable_sum _ fun i _ =>
      ((continuous_const.inner continuous_id).measurable.pow_const 2)).comp_aemeasurable hW_meas
      |>.congr (Eventually.of_forall fun ω => (hstat ω).symm)
  · have e : (fun ω => ⟪Ring.inverse S (V ω), V ω⟫) = (fun x => ∑ i, ⟪b i, x⟫ ^ 2) ∘ W :=
      funext hstat
    have hg : Measurable fun x : E => ∑ i, ⟪b i, x⟫ ^ 2 := by fun_prop
    have : Nonempty (Fin n) := ⟨⟨0, hd⟩⟩
    rw [e, ← AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hW_meas,
      hWlaw, stdGaussian_map_sum_sq_inner b Finset.univ_nonempty, Finset.card_univ,
      Fintype.card_fin]

end ChiSquare

/-! ### Maximum likelihood: asymptotic normality, Wald, score and likelihood-ratio tests -/

section Likelihood

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The inverse of a symmetric invertible operator is symmetric. -/
theorem inner_inverse_comm {S : E →L[ℝ] E} (hS_symm : ∀ u v, ⟪S u, v⟫ = ⟪u, S v⟫)
    (hS : IsUnit S) (u v : E) : ⟪Ring.inverse S u, v⟫ = ⟪u, Ring.inverse S v⟫ := by
  conv_lhs => rw [← apply_inverse_apply hS v]
  rw [← hS_symm, apply_inverse_apply hS]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem neg_inverse_neg_apply {S : E →L[ℝ] E} (hS : IsUnit S) (y : E) :
    -Ring.inverse (-S) y = Ring.inverse S y := by
  have h := inverse_apply_apply hS.neg (Ring.inverse S y)
  rw [neg_apply, apply_inverse_apply hS, map_neg] at h
  rw [← h]

omit [MeasurableSpace 𝓧] [MeasurableSpace E] [BorelSpace E] in
/-- **Second-order expansion of the log-likelihood** of one observation. If on the ball of
radius `δ` about `θ₀` the log-density `θ ↦ log p θ x` is differentiable (so `score p θ x` is
its true gradient) and the score is differentiable with
`‖Dscore θ x - Dscore θ₀ x‖ ≤ C ‖θ - θ₀‖`, then for `θ` in the ball
`|log p θ x - log p θ₀ x - ⟪score p θ₀ x, θ - θ₀⟫ - ⟪Dscore θ₀ x (θ - θ₀), θ - θ₀⟫ / 2|
  ≤ C ‖θ - θ₀‖³`. -/
theorem abs_log_sub_sub_sub_le {p : E → 𝓧 → ℝ} {θ₀ : E} {δ C : ℝ} {x : 𝓧}
    (hℓ_diff : ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => Real.log (p t x)) θ)
    (hs_diff : ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    (hC : ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => score p t x) θ - fderiv ℝ (fun t => score p t x) θ₀‖ ≤
        C * ‖θ - θ₀‖)
    {θ : E} (hθ : θ ∈ Metric.ball θ₀ δ) :
    |Real.log (p θ x) - Real.log (p θ₀ x) - ⟪score p θ₀ x, θ - θ₀⟫ -
        ⟪fderiv ℝ (fun t => score p t x) θ₀ (θ - θ₀), θ - θ₀⟫ / 2| ≤ C * ‖θ - θ₀‖ ^ 3 := by
  set h := θ - θ₀ with hh
  set H₀ := fderiv ℝ (fun t => score p t x) θ₀
  set s₀ := score p θ₀ x
  set ℓ : E → ℝ := fun t => Real.log (p t x) with hℓ
  have hmem : ∀ τ ∈ Set.Icc (0 : ℝ) 1, θ₀ + τ • h ∈ Metric.ball θ₀ δ := fun τ hτ => by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hτ.1]
    have hδ : ‖h‖ < δ := by rwa [Metric.mem_ball, dist_eq_norm] at hθ
    nlinarith [norm_nonneg h, hτ.2]
  set φ : ℝ → ℝ := fun τ => ℓ (θ₀ + τ • h) - τ * ⟪s₀, h⟫ - τ ^ 2 / 2 * ⟪H₀ h, h⟫ with hφ
  set φ' : ℝ → ℝ := fun τ => ⟪score p (θ₀ + τ • h) x, h⟫ - ⟪s₀, h⟫ - τ * ⟪H₀ h, h⟫ with hφ'
  have hderiv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ (φ' τ) (Set.Icc 0 1) τ :=
    fun τ hτ => by
      have hline : HasDerivAt (fun τ : ℝ => θ₀ + τ • h) h τ := by
        simpa using ((hasDerivAt_id τ).smul_const h).const_add θ₀
      have h1 : HasDerivAt (fun τ => ℓ (θ₀ + τ • h)) (fderiv ℝ ℓ (θ₀ + τ • h) h) τ :=
        HasFDerivAt.comp_hasDerivAt (l := ℓ) τ (hℓ_diff _ (hmem τ hτ)).hasFDerivAt hline
      have h1' : fderiv ℝ ℓ (θ₀ + τ • h) h = ⟪score p (θ₀ + τ • h) x, h⟫ := by
        rw [score, inner_gradient_left]
      rw [h1'] at h1
      have h2 : HasDerivAt (fun τ : ℝ => τ * ⟪s₀, h⟫) ⟪s₀, h⟫ τ := by
        simpa using (hasDerivAt_id τ).mul_const ⟪s₀, h⟫
      have h3 : HasDerivAt (fun τ : ℝ => τ ^ 2 / 2 * ⟪H₀ h, h⟫) (τ * ⟪H₀ h, h⟫) τ := by
        have := ((hasDerivAt_pow 2 τ).div_const 2).mul_const ⟪H₀ h, h⟫
        convert this using 1
        push_cast; ring
      exact ((h1.sub h2).sub h3).hasDerivWithinAt
  have hbound : ∀ τ ∈ Set.Ico (0 : ℝ) 1, ‖φ' τ‖ ≤ C * ‖h‖ ^ 3 := fun τ hτ => by
    have hτ' : τ ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hτ
    have e : φ' τ = ⟪score p (θ₀ + τ • h) x - s₀ - H₀ ((θ₀ + τ • h) - θ₀), h⟫ := by
      simp only [hφ', inner_sub_left, add_sub_cancel_left, map_smul, real_inner_smul_left]
    have htay := norm_sub_sub_fderiv_le (f := fun t => score p t x) hs_diff hC (hmem τ hτ')
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1] at htay
    rw [e, Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [add_sub_cancel_left] at *
    have hC0 : 0 ≤ C * ‖h‖ ^ 2 := by
      rcases (norm_nonneg h).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have := (norm_nonneg _).trans (hC θ hθ)
        rw [← hh] at this
        exact mul_nonneg (nonneg_of_mul_nonneg_left this hpos) (sq_nonneg _)
    calc ‖score p (θ₀ + τ • h) x - s₀ - H₀ (τ • h)‖ * ‖h‖
        ≤ C * (τ * ‖h‖) ^ 2 * ‖h‖ := mul_le_mul_of_nonneg_right htay (norm_nonneg h)
      _ = (τ ^ 2) * (C * ‖h‖ ^ 2) * ‖h‖ := by ring
      _ ≤ 1 * (C * ‖h‖ ^ 2) * ‖h‖ := by
          gcongr
          nlinarith [hτ.1, hτ.2]
      _ = C * ‖h‖ ^ 3 := by ring
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1
    (Set.right_mem_Icc.2 zero_le_one)
  have e1 : φ 1 - φ 0 = Real.log (p θ x) - Real.log (p θ₀ x) - ⟪s₀, h⟫ - ⟪H₀ h, h⟫ / 2 := by
    simp only [hφ, hℓ, one_smul, zero_smul, add_zero, hh, add_sub_cancel]
    ring
  rw [e1, Real.norm_eq_abs, sub_zero, mul_one] at hmvt
  exact hmvt

/-- **Asymptotic normality of consistent roots of the likelihood equation, vector parameter**
(Cramér's conditions; limit written as `I(θ₀)⁻¹ Y` with `Y ~ N(0, I(θ₀))`). For i.i.d.
observations with law `p θ₀ ν`, assume on the ball of radius `δ > 0` about the interior point
`θ₀` that the score `θ ↦ score p θ x` is differentiable with Lipschitz derivative
`‖Dscore θ x - Dscore θ₀ x‖ ≤ M x ‖θ - θ₀‖` (integrable `M`); that the score at `θ₀` is
measurable, square integrable and centered; that `Dscore θ₀` is strongly measurable, integrable
and satisfies the **information identity** `E Dscore θ₀ = -I(θ₀)`; and that the Fisher
information `I(θ₀)` is **nonsingular**. For estimators `θhat n` that are roots of the likelihood
equation `∑_{i<n} score p θ (X i) = 0` with probability tending to one and are consistent (both
are hypotheses: existence and consistency of the roots are not derived here; consistency of a
maximum-likelihood estimator follows, under compactness and identifiability, from Wald's theorem
`FisherInformation.ae_tendsto_maximumLikelihood`), `√n (θhat n - θ₀) → I(θ₀)⁻¹ Y`.

The centering and information identities are what differentiating `∫ p θ dν = 1` twice under
the integral sign gives; they are assumed directly.

Source: Cramér (1946), §33.3; Lehmann & Casella (1998), Theorem 6.5.1; van der Vaart (1998),
Theorem 5.41. -/
theorem tendstoInDistribution_sqrt_smul_sub_inverse_of_likelihoodEquation
    {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ₀ : E} {δ : ℝ} (hδ : 0 < δ)
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => score p t x) θ - fderiv ℝ (fun t => score p t x) θ₀‖ ≤
        M x * ‖θ - θ₀‖)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => ‖score p θ₀ x‖ ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂(lawOf ν p θ₀) = 0)
    (hs'_meas : StronglyMeasurable fun x => fderiv ℝ (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => fderiv ℝ (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, fderiv ℝ (fun t => score p t x) θ₀ ∂(lawOf ν p θ₀) =
      -fisherInformation ν p θ₀)
    (hI : IsUnit (fisherInformation ν p θ₀))
    {θhat : ℕ → Ω → E} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Y : Ω' → E} (hY_meas : AEMeasurable Y P')
    (hY : ∀ t, HasLaw (fun ω => ⟪Y ω, t⟫)
      (gaussianReal 0 (⟪fisherInformation ν p θ₀ t, t⟫).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √n • (θhat n ω - θ₀)) atTop
      (fun ω => Ring.inverse (fisherInformation ν p θ₀) (Y ω)) (fun _ => P) P' := by
  have hs : MemLp (score p θ₀) 2 (lawOf ν p θ₀) :=
    (memLp_two_iff_integrable_sq_norm hs_meas.aestronglyMeasurable).2 hs_sq
  have hvar : ∀ t, ∫ x, ⟪score p θ₀ x, t⟫ ^ 2 ∂(lawOf ν p θ₀) =
      ⟪fisherInformation ν p θ₀ t, t⟫ := fun t => by
    rw [inner_fisherInformation_apply hs]; simp_rw [sq]
  have h := tendstoInDistribution_sqrt_smul_sub_of_estimatingEquation hX_law hX_indep hδ
    hs_diff hM_meas hM_int hM hs_meas hs_sq hs_mean hs'_meas hs'_int
    (by rw [h_info]; exact hI.neg) hθ_meas hroot hcons hY_meas
    (fun t => by rw [hvar]; exact hY t)
  rw [h_info] at h
  exact h.congr (fun n => ae_of_all _ fun ω => rfl)
    (ae_of_all _ fun ω => neg_inverse_neg_apply hI (Y ω))

/-- **Asymptotic normality of maximum likelihood, vector parameter**:
`√n (θhat n - θ₀) → N(0, I(θ₀)⁻¹)` in distribution, the limit being any random vector `Z`
with `⟪Z, t⟫ ~ N(0, ⟪I(θ₀)⁻¹ t, t⟫)`. Hypotheses as in
`tendstoInDistribution_sqrt_smul_sub_inverse_of_likelihoodEquation`; the Gaussian
`N(0, I(θ₀))` needed there is constructed from the score by the multivariate CLT machinery.

Source: Cramér (1946), §33.3; Lehmann & Casella (1998), Theorem 6.5.1; van der Vaart (1998),
Theorem 5.41. -/
theorem tendstoInDistribution_sqrt_smul_sub_of_likelihoodEquation
    {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ₀ : E} {δ : ℝ} (hδ : 0 < δ)
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => score p t x) θ - fderiv ℝ (fun t => score p t x) θ₀‖ ≤
        M x * ‖θ - θ₀‖)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => ‖score p θ₀ x‖ ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂(lawOf ν p θ₀) = 0)
    (hs'_meas : StronglyMeasurable fun x => fderiv ℝ (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => fderiv ℝ (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, fderiv ℝ (fun t => score p t x) θ₀ ∂(lawOf ν p θ₀) =
      -fisherInformation ν p θ₀)
    (hI : IsUnit (fisherInformation ν p θ₀))
    {θhat : ℕ → Ω → E} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Z : Ω' → E} (hZ_meas : AEMeasurable Z P')
    (hZ : ∀ t, HasLaw (fun ω => ⟪Z ω, t⟫)
      (gaussianReal 0 (⟪Ring.inverse (fisherInformation ν p θ₀) t, t⟫).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √n • (θhat n ω - θ₀)) atTop Z (fun _ => P) P' := by
  set I := fisherInformation ν p θ₀
  set K := Ring.inverse I
  have hs : MemLp (score p θ₀) 2 (lawOf ν p θ₀) :=
    (memLp_two_iff_integrable_sq_norm hs_meas.aestronglyMeasurable).2 hs_sq
  obtain ⟨A, hA⟩ := exists_hasLaw_inner_gaussianReal ((hX_law 0).memLp_comp hs)
  have hAI : ∀ t, HasLaw (fun z => ⟪A z, t⟫) (gaussianReal 0 (⟪I t, t⟫).toNNReal)
      (stdGaussian E) := fun t => by
    have h := hA t
    rwa [show (fun ω => ⟪(score p θ₀ ∘ X 0) ω, t⟫) = fun ω => ⟪score p θ₀ (X 0 ω), t⟫ from rfl,
      variance_inner_score (hX_law 0) hs_meas hs_sq hs_mean t] at h
  have h := tendstoInDistribution_sqrt_smul_sub_inverse_of_likelihoodEquation hδ hX_law
    hX_indep hs_diff hM_meas hM_int hM hs_meas hs_sq hs_mean hs'_meas hs'_int h_info hI
    hθ_meas hroot hcons A.continuous.aemeasurable hAI
  refine h.of_map_eq hZ_meas (map_eq_of_forall_map_inner (by fun_prop) hZ_meas fun t => ?_)
  rw [(hZ t).map_eq]
  have e : (fun z => ⟪K (A z), t⟫) = fun z => ⟪A z, K t⟫ := funext fun z =>
    inner_inverse_comm (inner_fisherInformation_comm ν p θ₀) hI _ _
  rw [e, (hAI (K t)).map_eq, apply_inverse_apply hI, real_inner_comm]

/-- **Wald's test, vector parameter.** Under the hypotheses of
`tendstoInDistribution_sqrt_smul_sub_of_likelihoodEquation`, with the information positive
definite (hence nonsingular) and `d = dim E ≥ 1`, the Wald statistic
`n ⟪I(θ₀) (θhat n - θ₀), θhat n - θ₀⟫`, built with the null information `I(θ₀)` (not `I(θhat n)`
or the observed information), converges in distribution to `χ²_d`.

Source: Wald (1943); van der Vaart (1998), ch. 16. -/
theorem tendstoInDistribution_waldStatistic
    {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ₀ : E} {δ : ℝ} (hδ : 0 < δ)
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => score p t x) θ - fderiv ℝ (fun t => score p t x) θ₀‖ ≤
        M x * ‖θ - θ₀‖)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => ‖score p θ₀ x‖ ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂(lawOf ν p θ₀) = 0)
    (hs'_meas : StronglyMeasurable fun x => fderiv ℝ (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => fderiv ℝ (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, fderiv ℝ (fun t => score p t x) θ₀ ∂(lawOf ν p θ₀) =
      -fisherInformation ν p θ₀)
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪fisherInformation ν p θ₀ u, u⟫)
    (hd : 0 < Module.finrank ℝ E)
    {θhat : ℕ → Ω → E} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Module.finrank ℝ E)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => n * ⟪fisherInformation ν p θ₀ (θhat n ω - θ₀), θhat n ω - θ₀⟫)
      atTop Q (fun _ => P) P' := by
  set I := fisherInformation ν p θ₀
  have hI : IsUnit I := isUnit_of_inner_self_pos hI_pos
  have hs : MemLp (score p θ₀) 2 (lawOf ν p θ₀) :=
    (memLp_two_iff_integrable_sq_norm hs_meas.aestronglyMeasurable).2 hs_sq
  obtain ⟨A, hA⟩ := exists_hasLaw_inner_gaussianReal ((hX_law 0).memLp_comp hs)
  have hAI : ∀ t, HasLaw (fun z => ⟪A z, t⟫) (gaussianReal 0 (⟪I t, t⟫).toNNReal)
      (stdGaussian E) := fun t => by
    have h := hA t
    rwa [show (fun ω => ⟪(score p θ₀ ∘ X 0) ω, t⟫) = fun ω => ⟪score p θ₀ (X 0 ω), t⟫ from rfl,
      variance_inner_score (hX_law 0) hs_meas hs_sq hs_mean t] at h
  have h := tendstoInDistribution_sqrt_smul_sub_inverse_of_likelihoodEquation hδ hX_law
    hX_indep hs_diff hM_meas hM_int hM hs_meas hs_sq hs_mean hs'_meas hs'_int h_info hI
    hθ_meas hroot hcons A.continuous.aemeasurable hAI
  have h2 := h.continuous_comp (g := fun v => ⟪I v, v⟫) (by fun_prop)
  have hchi := hasLaw_inner_inverse_chiSquare (inner_fisherInformation_comm ν p θ₀) hI_pos hd
    A.continuous.aemeasurable hAI
  refine (h2.congr (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun z => rfl)).of_map_eq
    hQ.aemeasurable ?_
  · simp only [Function.comp_apply, map_smul, real_inner_smul_left, real_inner_smul_right]
    rw [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  · rw [hQ.map_eq, ← hchi.map_eq]
    congr 1
    funext z
    simp only [Function.comp_apply]
    rw [apply_inverse_apply hI, real_inner_comm]

/-- **Rao's score test, vector parameter.** For i.i.d. observations with law `p θ₀ ν`, a
measurable, centered, square-integrable score and positive definite Fisher information
`I(θ₀)` (with `d = dim E ≥ 1`), the score statistic `⟪I(θ₀)⁻¹ Sₙ, Sₙ⟫` (null information),
`Sₙ = n^{-1/2} ∑_{i<n} score p θ₀ (X i)`, converges in distribution to `χ²_d`.

Source: Rao (1948); van der Vaart (1998), ch. 16. -/
theorem tendstoInDistribution_scoreStatistic {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ₀ : E}
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => ‖score p θ₀ x‖ ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂(lawOf ν p θ₀) = 0)
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪fisherInformation ν p θ₀ u, u⟫)
    (hd : 0 < Module.finrank ℝ E)
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Module.finrank ℝ E)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ⟪Ring.inverse (fisherInformation ν p θ₀)
            ((√n)⁻¹ • ∑ i ∈ Finset.range n, score p θ₀ (X i ω)),
          (√n)⁻¹ • ∑ i ∈ Finset.range n, score p θ₀ (X i ω)⟫)
      atTop Q (fun _ => P) P' := by
  set I := fisherInformation ν p θ₀
  have hs : MemLp (score p θ₀) 2 (lawOf ν p θ₀) :=
    (memLp_two_iff_integrable_sq_norm hs_meas.aestronglyMeasurable).2 hs_sq
  obtain ⟨A, hA⟩ := exists_hasLaw_inner_gaussianReal ((hX_law 0).memLp_comp hs)
  have hAI : ∀ t, HasLaw (fun z => ⟪A z, t⟫) (gaussianReal 0 (⟪I t, t⟫).toNNReal)
      (stdGaussian E) := fun t => by
    have h := hA t
    rwa [show (fun ω => ⟪(score p θ₀ ∘ X 0) ω, t⟫) = fun ω => ⟪score p θ₀ (X 0 ω), t⟫ from rfl,
      variance_inner_score (hX_law 0) hs_meas hs_sq hs_mean t] at h
  have h := tendstoInDistribution_score hX_law hX_indep hs_meas hs_sq hs_mean
    A.continuous.aemeasurable hAI
  have h2 := h.continuous_comp (g := fun v => ⟪Ring.inverse I v, v⟫) (by fun_prop)
  have hchi := hasLaw_inner_inverse_chiSquare (inner_fisherInformation_comm ν p θ₀) hI_pos hd
    A.continuous.aemeasurable hAI
  exact h2.of_map_eq hQ.aemeasurable (by rw [hQ.map_eq, ← hchi.map_eq]; rfl)

/-- **Wilks' theorem, vector parameter, simple null.** Under the hypotheses of
`tendstoInDistribution_waldStatistic`, if moreover the log-density `θ ↦ log p θ x` is
differentiable on the ball (so the score is its true gradient there) and `(θ, x) ↦ p θ x` is
jointly measurable, then the likelihood-ratio statistic
`2 (ℓₙ(θhat n) - ℓₙ(θ₀))`, `ℓₙ θ = ∑_{i<n} log p θ (X i)`, evaluated at the consistent root
`θhat n` (not the supremum `sup_θ ℓₙ θ`), converges in distribution to `χ²_d`, `d = dim E ≥ 1`.
Composite nulls with `r` restrictions (limit `χ²_r`) are not covered.

The proof expands `ℓₙ` to second order around `θ₀` (`abs_log_sub_sub_sub_le`) and shows
`2 (ℓₙ(θhat n) - ℓₙ(θ₀)) - n ⟪I(θ₀) (θhat n - θ₀), θhat n - θ₀⟫ → 0` in probability.

Source: Wilks (1938); van der Vaart (1998), Theorem 16.7. -/
theorem tendstoInDistribution_two_mul_logLikelihood_sub
    {ν : Measure 𝓧} {p : E → 𝓧 → ℝ} {θ₀ : E} {δ : ℝ} (hδ : 0 < δ)
    (hp_meas : Measurable (Function.uncurry p))
    {X : ℕ → Ω → 𝓧} (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    (hℓ_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => Real.log (p t x)) θ)
    (hs_diff : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ, DifferentiableAt ℝ (fun t => score p t x) θ)
    {M : 𝓧 → ℝ} (hM_meas : Measurable M) (hM_int : Integrable M (lawOf ν p θ₀))
    (hM : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => score p t x) θ - fderiv ℝ (fun t => score p t x) θ₀‖ ≤
        M x * ‖θ - θ₀‖)
    (hs_meas : Measurable (score p θ₀))
    (hs_sq : Integrable (fun x => ‖score p θ₀ x‖ ^ 2) (lawOf ν p θ₀))
    (hs_mean : ∫ x, score p θ₀ x ∂(lawOf ν p θ₀) = 0)
    (hs'_meas : StronglyMeasurable fun x => fderiv ℝ (fun t => score p t x) θ₀)
    (hs'_int : Integrable (fun x => fderiv ℝ (fun t => score p t x) θ₀) (lawOf ν p θ₀))
    (h_info : ∫ x, fderiv ℝ (fun t => score p t x) θ₀ ∂(lawOf ν p θ₀) =
      -fisherInformation ν p θ₀)
    (hI_pos : ∀ u, u ≠ 0 → 0 < ⟪fisherInformation ν p θ₀ u, u⟫)
    (hd : 0 < Module.finrank ℝ E)
    {θhat : ℕ → Ω → E} (hθ_meas : ∀ n, AEMeasurable (θhat n) P)
    (hroot : Tendsto (fun n => P {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) ≠ 0})
      atTop (𝓝 0))
    (hcons : TendstoInMeasure P θhat atTop (fun _ => θ₀))
    {Q : Ω' → ℝ} (hQ : HasLaw Q (chiSquareMeasure (Module.finrank ℝ E)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => 2 * ∑ i ∈ Finset.range n,
        (Real.log (p (θhat n ω) (X i ω)) - Real.log (p θ₀ (X i ω))))
      atTop Q (fun _ => P) P' := by
  set I := fisherInformation ν p θ₀
  have hI : IsUnit I := isUnit_of_inner_self_pos hI_pos
  have : IsProbabilityMeasure (lawOf ν p θ₀) := (hX_law 0).isProbabilityMeasure_iff.1 inferInstance
  have hXm : ∀ i, AEMeasurable (X i) P := fun i => (hX_law i).aemeasurable
  have hs : MemLp (score p θ₀) 2 (lawOf ν p θ₀) :=
    (memLp_two_iff_integrable_sq_norm hs_meas.aestronglyMeasurable).2 hs_sq
  obtain ⟨A, hA⟩ := exists_hasLaw_inner_gaussianReal ((hX_law 0).memLp_comp hs)
  have hAI : ∀ t, HasLaw (fun z => ⟪A z, t⟫) (gaussianReal 0 (⟪I t, t⟫).toNNReal)
      (stdGaussian E) := fun t => by
    have h := hA t
    rwa [show (fun ω => ⟪(score p θ₀ ∘ X 0) ω, t⟫) = fun ω => ⟪score p θ₀ (X 0 ω), t⟫ from rfl,
      variance_inner_score (hX_law 0) hs_meas hs_sq hs_mean t] at h
  have hT := tendstoInDistribution_sqrt_smul_sub_inverse_of_likelihoodEquation hδ hX_law
    hX_indep hs_diff hM_meas hM_int hM hs_meas hs_sq hs_mean hs'_meas hs'_int h_info hI
    hθ_meas hroot hcons A.continuous.aemeasurable hAI
  have hW := tendstoInDistribution_waldStatistic hδ hX_law hX_indep hs_diff hM_meas hM_int hM
    hs_meas hs_sq hs_mean hs'_meas hs'_int h_info hI_pos hd hθ_meas hroot hcons hQ
  -- notation
  set H : 𝓧 → E →L[ℝ] E := fun x => fderiv ℝ (fun t => score p t x) θ₀ with hH_def
  set M' : 𝓧 → ℝ := fun x => |M x| with hM'_def
  have hM'_meas : Measurable M' := continuous_abs.measurable.comp hM_meas
  have hM'_int : Integrable M' (lawOf ν p θ₀) := hM_int.abs
  have hM'0 : ∀ x, 0 ≤ M' x := fun x => abs_nonneg _
  have hM' : ∀ x, ∀ θ ∈ Metric.ball θ₀ δ,
      ‖fderiv ℝ (fun t => score p t x) θ - fderiv ℝ (fun t => score p t x) θ₀‖ ≤
        M' x * ‖θ - θ₀‖ :=
    fun x θ hθ => (hM x θ hθ).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  set L : ℕ → Ω → ℝ := fun n ω => 2 * ∑ i ∈ Finset.range n,
    (Real.log (p (θhat n ω) (X i ω)) - Real.log (p θ₀ (X i ω))) with hL_def
  set W : ℕ → Ω → ℝ := fun n ω => n * ⟪I (θhat n ω - θ₀), θhat n ω - θ₀⟫ with hW_def
  set T : ℕ → Ω → E := fun n ω => √n • (θhat n ω - θ₀) with hT_def
  set B : ℕ → Ω → E →L[ℝ] E := fun n ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, H (X i ω)
    with hB_def
  set Mb : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, M' (X i ω) with hMb_def
  set η : ℕ → Ω → ℝ := fun n ω => ‖B n ω - (-I)‖ + 4 * (‖θhat n ω - θ₀‖ * Mb n ω) with hη_def
  -- measurability
  have hB_sm : ∀ n, AEStronglyMeasurable (B n) P := fun n => by
    have h : AEStronglyMeasurable (fun ω => ∑ i ∈ Finset.range n, H (X i ω)) P :=
      Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        hs'_meas.aestronglyMeasurable.comp_aemeasurable (hXm i)
    exact h.const_smul ((n : ℝ)⁻¹)
  have hMb_meas : ∀ n, AEMeasurable (Mb n) P := fun n => by
    have h : AEMeasurable (fun ω => ∑ i ∈ Finset.range n, M' (X i ω)) P :=
      Finset.aemeasurable_fun_sum _ fun i _ => hM'_meas.comp_aemeasurable (hXm i)
    exact h.const_mul ((n : ℝ)⁻¹)
  have hη_meas : ∀ n, AEMeasurable (η n) P := fun n =>
    ((hB_sm n).sub aestronglyMeasurable_const).norm.aemeasurable.add
      ((((hθ_meas n).sub_const _).norm.mul (hMb_meas n)).const_mul 4)
  have hL_meas : ∀ n, AEMeasurable (L n) P := fun n => by
    have hlog : Measurable fun q : E × 𝓧 => Real.log (Function.uncurry p q) :=
      Real.measurable_log.comp hp_meas
    refine (Finset.aemeasurable_fun_sum _ fun i _ => ?_).const_mul 2
    exact (hlog.comp_aemeasurable ((hθ_meas n).prodMk (hXm i))).sub
      (hlog.comp_aemeasurable (aemeasurable_const.prodMk (hXm i)))
  -- laws of large numbers
  have hB : TendstoInMeasure P B atTop (fun _ => -I) := by
    have h := tendstoInMeasure_of_tendsto_ae hB_sm
      (ae_tendsto_average hX_law hX_indep hs'_meas hs'_int)
    rwa [h_info] at h
  have hMb : TendstoInMeasure P Mb atTop (fun _ => ∫ x, M' x ∂(lawOf ν p θ₀)) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hMb_meas n).aestronglyMeasurable)
      (ae_tendsto_average hX_law hX_indep hM'_meas.stronglyMeasurable hM'_int)
  have hBD : TendstoInMeasure P (fun n ω => ‖B n ω - (-I)‖) atTop 0 := by
    rw [tendstoInMeasure_iff_norm] at hB ⊢
    simpa using hB
  have hdθ : TendstoInMeasure P (fun n ω => ‖θhat n ω - θ₀‖) atTop 0 := by
    rw [tendstoInMeasure_iff_norm] at hcons ⊢
    simpa using hcons
  have hrem : TendstoInMeasure P (fun n ω => 4 * (‖θhat n ω - θ₀‖ * Mb n ω)) atTop 0 := by
    have h := (hMb.tendstoInDistribution_of_aemeasurable hMb_meas aemeasurable_const
      ).mul_tendstoInMeasure_zero hdθ (fun n => ((hθ_meas n).sub_const _).norm)
    have h' : TendstoInMeasure P (fun n ω => ‖θhat n ω - θ₀‖ * Mb n ω) atTop 0 := by
      simpa only [mul_comm] using h
    rw [tendstoInMeasure_iff_norm] at h' ⊢
    intro ε hε
    refine (h' (ε / 4) (by positivity)).congr fun n => ?_
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    constructor <;> intro h <;> linarith
  have hη : TendstoInMeasure P η atTop 0 := tendstoInMeasure_add_zero' hBD hrem
  -- good events
  set G : ℕ → Set Ω := fun n => {ω | ∑ i ∈ Finset.range n, score p (θhat n ω) (X i ω) = 0} ∩
    {ω | ‖θhat n ω - θ₀‖ < δ} with hG_def
  have hG : Tendsto (fun n => P (G n)ᶜ) atTop (𝓝 0) := by
    have h1 := (tendstoInMeasure_iff_dist.1 hcons) δ hδ
    have h3 := hroot.add h1
    simp only [add_zero] at h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => zero_le)
      fun n => ?_
    refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
    simp only [hG_def, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, not_and_or,
      not_lt] at hω
    simp only [Set.mem_union, Set.mem_ofPred_eq, dist_eq_norm]
    exact hω
  -- deterministic bound on the good events
  have hbound : ∀ n, ∀ ω ∈ G n, |L n ω - W n ω| ≤ ‖T n ω‖ ^ 2 * η n ω := by
    intro n ω hω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hL_def, hW_def, hT_def]
    obtain ⟨hroot', hclose⟩ := hω
    simp only [Set.mem_ofPred_eq] at hroot' hclose
    have hball : θhat n ω ∈ Metric.ball θ₀ δ := by
      rw [Metric.mem_ball, dist_eq_norm]; exact hclose
    set d := θhat n ω - θ₀ with hd
    set S0 := ∑ i ∈ Finset.range n, score p θ₀ (X i ω) with hS0
    set Hs := ∑ i ∈ Finset.range n, H (X i ω) with hHs_def
    set SM := ∑ i ∈ Finset.range n, M' (X i ω) with hSM_def
    set e : ℕ → ℝ := fun i => Real.log (p (θhat n ω) (X i ω)) - Real.log (p θ₀ (X i ω)) -
      ⟪score p θ₀ (X i ω), d⟫ - ⟪H (X i ω) d, d⟫ / 2 with he_def
    have he : ∀ i, |e i| ≤ M' (X i ω) * ‖d‖ ^ 3 := fun i =>
      abs_log_sub_sub_sub_le (hℓ_diff (X i ω)) (hs_diff (X i ω)) (hM' (X i ω)) hball
    have htay : ‖S0 + Hs d‖ ≤ SM * ‖d‖ ^ 2 :=
      norm_sum_add_sum_apply_le hs_diff hM' n (fun i => X i ω) hball hroot'
    have hid : L n ω - W n ω =
        2 * ∑ i ∈ Finset.range n, e i + 2 * ⟪S0 + Hs d, d⟫ - ⟪(Hs + (n : ℝ) • I) d, d⟫ := by
      simp only [hL_def, hW_def, he_def, hS0, hHs_def, add_apply, smul_apply, inner_add_left,
        real_inner_smul_left, sum_apply, sum_inner, Finset.sum_sub_distrib, ← Finset.sum_div]
      ring
    have h1 : |∑ i ∈ Finset.range n, e i| ≤ SM * ‖d‖ ^ 3 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [hSM_def, Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => he i
    have h2 : |⟪S0 + Hs d, d⟫| ≤ SM * ‖d‖ ^ 3 := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      calc ‖S0 + Hs d‖ * ‖d‖ ≤ SM * ‖d‖ ^ 2 * ‖d‖ :=
            mul_le_mul_of_nonneg_right htay (norm_nonneg _)
        _ = SM * ‖d‖ ^ 3 := by ring
    have h3 : |⟪(Hs + (n : ℝ) • I) d, d⟫| ≤ ‖Hs + (n : ℝ) • I‖ * ‖d‖ ^ 2 := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      calc ‖(Hs + (n : ℝ) • I) d‖ * ‖d‖ ≤ ‖Hs + (n : ℝ) • I‖ * ‖d‖ * ‖d‖ :=
            mul_le_mul_of_nonneg_right ((Hs + (n : ℝ) • I).le_opNorm d) (norm_nonneg _)
        _ = ‖Hs + (n : ℝ) • I‖ * ‖d‖ ^ 2 := by ring
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hSM : SM = n * Mb n ω := by
      simp only [hMb_def, smul_eq_mul, hSM_def]
      field_simp
    have hHs : Hs + (n : ℝ) • I = (n : ℝ) • (B n ω - -I) := by
      simp only [hB_def, sub_neg_eq_add, smul_add, smul_smul, mul_inv_cancel₀ hn0, one_smul,
        hHs_def]
    have hT2 : ‖T n ω‖ ^ 2 = n * ‖d‖ ^ 2 := by
      simp only [hT_def, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      rfl
    rw [hid]
    obtain ⟨h1l, h1r⟩ := abs_le.1 h1
    obtain ⟨h2l, h2r⟩ := abs_le.1 h2
    obtain ⟨h3l, h3r⟩ := abs_le.1 h3
    have hfin : 2 * (SM * ‖d‖ ^ 3) + 2 * (SM * ‖d‖ ^ 3) + ‖Hs + (n : ℝ) • I‖ * ‖d‖ ^ 2 =
        ‖T n ω‖ ^ 2 * η n ω := by
      rw [hHs, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < n), hSM, hT2]
      simp only [hη_def]
      ring
    rw [← hfin, abs_le]
    constructor <;> linarith
  -- conclusion
  have hV : TendstoInMeasure P (fun n ω => ‖T n ω‖ ^ 2 * η n ω) atTop 0 :=
    (hT.continuous_comp (g := fun v => ‖v‖ ^ 2) (by fun_prop)).mul_tendstoInMeasure_zero hη
      hη_meas
  have hdiff : TendstoInMeasure P (fun n ω => L n ω - W n ω) atTop 0 :=
    tendstoInMeasure_zero_of_abs_le hV hG hbound
  exact tendstoInDistribution_of_tendstoInMeasure_sub L Q hW hdiff hL_meas

end Likelihood

end MathlibExt.Probability.Statistics.VectorInference
