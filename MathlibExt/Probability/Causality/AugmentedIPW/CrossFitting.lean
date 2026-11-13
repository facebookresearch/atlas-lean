/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.AugmentedIPW.DoubleRobustness
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.CentralLimitTheorem

/-!
# Cross-fitted AIPW: double robustness and asymptotic normality

Cross-fitting (sample splitting, double/debiased machine learning) estimates the average
treatment effect `E[Y₁ - Y₀]` by splitting the sample into folds, fitting the nuisances
(propensity `ê`, outcome regressions `ĝ₀, ĝ₁`) on all folds but one, and averaging the AIPW
score `aipwScoreOfSigma` at those fitted nuisances over the held-out fold. Because a held-out
unit is independent of the data its nuisances were fitted on, the analysis needs no Donsker or
entropy condition on the nuisance estimators: the remainder is the product of nuisance errors.

## Main definitions

* `aipwRemainder μ m T Y₀ Y₁ e g₀ g₁`: the bias
  `E[(e* - e) ((μ₁* - g₁) / e + (μ₀* - g₀) / (1 - e))]` of the AIPW score at candidate
  nuisances, `e* = P(T | m)`, `μₐ* = E[Yₐ | m]`.
* `evalFold`, `trainFold`, `trainData`: the evaluation indices, training indices and training data
  of fold `k` at sample size `n`, for a fold assignment `fold : ℕ → ℕ → Fin K`.
* `crossFitEstimator W fold G n`: `n⁻¹ ∑_{i < n} G n (fold n i) (trainData (fold n i), W i)`, each
  unit scored at the nuisances fitted on the training data of its own fold.

## Main results

Double robustness with sample-split nuisances (population level, general covariate σ-algebra):
* `integral_crossFit_sub`: the joint mean of the score over (training sample, evaluation unit)
  minus the ATE is the training-mean of `aipwRemainder` at the fitted nuisances.
* `integral_crossFit_eq`: unbiasedness when, for almost every training sample, the fitted
  propensity or both fitted outcome regressions are correct.
* `abs_aipwRemainder_le`: `|aipwRemainder| ≤ ε⁻¹ ‖e* - e‖₂ (‖μ₁* - g₁‖₂ + ‖μ₀* - g₀‖₂)`.

Cross-fitting removes the Donsker condition:
* `integral_sq_sum_of_indep`: for a kernel centered given the training data,
  `E[(∑_{i ∈ s} D(U, V i))²] = |s| E[D²]`, from independence alone.
* `measureReal_le_of_indep`, `tendstoInMeasure_crossFit_empirical`: a conditional Chebyshev bound;
  the split-sample empirical process term tends to `0` in probability when the conditional `L²`
  error of the fitted score does.

Asymptotic normality:
* `tendstoInMeasure_crossFitEstimator_sub_oracle`: `√n (θ̂ₙ - θ̂ₙ*) → 0` in probability, with
  `θ̂ₙ*` the oracle estimator at the true nuisances, under `L²` consistency of the fitted score and
  `√n`-negligible bias.
* `tendstoInDistribution_of_tendstoInMeasure_oracle_gap`: the oracle gap plus the CLT gives
  `√n (θ̂ₙ - θ) → N(0, Var ψ)` (Slutsky).
* `tendstoInDistribution_crossFitEstimator`: the generic DML theorem.
* `tendstoInMeasure_crossFit_aipw_sub_oracle`, `tendstoInDistribution_crossFit_aipw`: the AIPW
  instance, with the bias condition replaced by the product rate
  `√n ‖e* - ê‖₂ (‖μ₁* - ĝ₁‖₂ + ‖μ₀* - ĝ₀‖₂) → 0` in probability.

## Hypotheses and scope

* The fitted score's `L²` consistency (`∫ (ψ(ê, ĝ) - ψ*)² dν → 0` in probability) is a hypothesis,
  as in the regularity conditions of Chernozhukov et al. (2018); deriving it from nuisance
  consistency (it needs, e.g., a bounded conditional outcome variance) is not done here.
* Fitted propensities are clipped to `[ε, 1 - ε]` for every training sample, the true propensity
  satisfies strong overlap, and fitted nuisances are square integrable for every training sample.
* Joint integrability of the score on (training × evaluation) is a hypothesis of the
  population-level identities, needed for Fubini, as in
  `Orthogonality.integral_aipwScore_splitfold_tower`.
* Folds are arbitrary: `fold n` may depend on `n` and folds need not be balanced; only
  `|evalFold| ≤ n` is used. The fold count `K` is fixed.
* The training data are full-data observations, so a fitting rule may in principle read any
  coordinate; estimators that read only the observed `(T, X, Y)` are a special case. The fitted
  nuisances must be `m`-measurable in the evaluation point, i.e. functions of the covariates.
* Variance estimation and confidence intervals are not covered.

## Relation to the merged AIPW files (API-00)

* The score is `aipwScoreOfSigma` (`DoubleRobustness`), i.e. `MissingOutcomes.aipwATEScore`;
  the fiberwise bias identity is `integral_aipwScoreOfSigma_sub` and the oracle mean is
  `integral_aipwScoreOfSigma_of_propensity`.
* `Orthogonality` proves first-order Neyman orthogonality and the sample-split tower identity for a
  finite covariate and a missing-outcome mean. `integral_crossFit_sub` is the corresponding tower
  identity for the ATE score with an arbitrary covariate σ-algebra; the rate analysis here uses the
  second-order bound `abs_aipwRemainder_le` rather than a derivative.
* Mathlib supplies the CLT (`tendstoInDistribution_inv_sqrt_mul_sum_sub`) and Slutsky's lemma
  (`tendstoInDistribution_of_tendstoInMeasure_sub`).
* `tendstoInMeasure_crossFit_aipw_sub_oracle` is stated in the shape of the remainder hypothesis
  `hrem` (`√n (τ̂ - τ̂*) → 0` in probability) of the T143 oracle-AIPW asymptotic-normality
  development; see its docstring.

## References

* V. Chernozhukov, D. Chetverikov, M. Demirer, E. Duflo, C. Hansen, W. Newey and J. Robins,
  *Double/debiased machine learning for treatment and structural parameters*, Econometrics
  Journal 21(1) (2018), C1–C68: the cross-fitted estimator, the regularity conditions on the
  fitted score (`L²` rate `r_N`, bias of order `o(N^{-1/2})`), and the ATE application.
* E. H. Kennedy, *Semiparametric doubly robust targeted double machine learning: a review*,
  arXiv:2203.06469v2 (2023): sample splitting in place of Donsker conditions, and the product
  form of the AIPW remainder.
* J. M. Robins, A. Rotnitzky and L. P. Zhao, *Estimation of regression coefficients when some
  regressors are not always observed*, JASA 89(427) (1994), 846–866.
-/

@[expose] public section

namespace MathlibExt.Probability.Causality.AugmentedIPW.CrossFitting

open MeasureTheory MathlibExt.Probability.Causality

section Remainder

variable {Ω : Type*} {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The **AIPW remainder** at candidate nuisances `e, g₀, g₁`, with `m` the covariate
σ-algebra: `E[(e* - e) ((μ₁* - g₁) / e + (μ₀* - g₀) / (1 - e))]`, where `e* = P(T | m)`,
`μ₀* = E[Y₀ | m]` and `μ₁* = E[Y₁ | m]`. By `integral_aipwScoreOfSigma_sub` it is the bias
`E[ψ] - E[Y₁ - Y₀]` of the AIPW score at these nuisances; it is a product of the propensity
error and the outcome-regression errors. -/
noncomputable def aipwRemainder (μ : Measure Ω) (m : MeasurableSpace Ω) (T : Set Ω)
    (Y₀ Y₁ e g₀ g₁ : Ω → ℝ) : ℝ :=
  ∫ ω, (μ[T.indicator 1 | m] ω - e ω) *
    ((μ[Y₁ | m] ω - g₁ ω) / e ω + (μ[Y₀ | m] ω - g₀ ω) / (1 - e ω)) ∂μ

/-- Cauchy–Schwarz in the form used for the remainder bound. -/
private lemma integral_abs_mul_abs_le {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ ω, |f ω| * |g ω| ∂μ ≤ √(∫ ω, f ω ^ 2 ∂μ) * √(∫ ω, g ω ^ 2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
    (f := f) (g := g) (by simpa using hf) (by simpa using hg)
  simpa [Real.norm_eq_abs, Real.sqrt_eq_rpow, Real.rpow_two, sq_abs] using h

variable {T : Set Ω} {Y₀ Y₁ e g₀ g₁ : Ω → ℝ}

/-- The remainder vanishes when the candidate propensity is correct, `e = P(T | m)` a.e. -/
theorem aipwRemainder_eq_zero_of_propensity (hprop : e =ᵐ[μ] μ[T.indicator 1 | m]) :
    aipwRemainder μ m T Y₀ Y₁ e g₀ g₁ = 0 := by
  rw [aipwRemainder, ← integral_zero Ω ℝ]
  refine integral_congr_ae ?_
  filter_upwards [hprop] with ω h
  simp [h]

/-- The remainder vanishes when both candidate outcome regressions are correct,
`g₀ = E[Y₀ | m]` and `g₁ = E[Y₁ | m]` a.e. -/
theorem aipwRemainder_eq_zero_of_outcome (hout₀ : g₀ =ᵐ[μ] μ[Y₀ | m])
    (hout₁ : g₁ =ᵐ[μ] μ[Y₁ | m]) :
    aipwRemainder μ m T Y₀ Y₁ e g₀ g₁ = 0 := by
  rw [aipwRemainder, ← integral_zero Ω ℝ]
  refine integral_congr_ae ?_
  filter_upwards [hout₀, hout₁] with ω h₀ h₁
  simp [h₀, h₁]

/-- **The remainder is bounded by a product of `L²` nuisance errors.** If
`ε ≤ e ≤ 1 - ε` a.e., then
`|aipwRemainder| ≤ ε⁻¹ ‖e* - e‖₂ (‖μ₁* - g₁‖₂ + ‖μ₀* - g₀‖₂)`, with `e* = P(T | m)`,
`μₐ* = E[Yₐ | m]`. This is the mixed-bias bound: the bias is second order, a product of the
propensity error and the outcome-regression errors. -/
theorem abs_aipwRemainder_le [IsFiniteMeasure μ] (hT : MeasurableSet[mΩ] T)
    (hY₀ : MemLp Y₀ 2 μ) (hY₁ : MemLp Y₁ 2 μ) (he : AEStronglyMeasurable[mΩ] e μ)
    (hg₀ : MemLp g₀ 2 μ) (hg₁ : MemLp g₁ 2 μ) {ε : ℝ} (hε : 0 < ε)
    (heε : ∀ᵐ ω ∂μ, ε ≤ e ω ∧ e ω ≤ 1 - ε) :
    |aipwRemainder μ m T Y₀ Y₁ e g₀ g₁| ≤
      ε⁻¹ * √(∫ ω, (μ[T.indicator 1 | m] ω - e ω) ^ 2 ∂μ) *
        (√(∫ ω, (μ[Y₁ | m] ω - g₁ ω) ^ 2 ∂μ) + √(∫ ω, (μ[Y₀ | m] ω - g₀ ω) ^ 2 ∂μ)) := by
  set a : Ω → ℝ := fun ω => μ[T.indicator 1 | m] ω - e ω
  set b₁ : Ω → ℝ := fun ω => μ[Y₁ | m] ω - g₁ ω
  set b₀ : Ω → ℝ := fun ω => μ[Y₀ | m] ω - g₀ ω
  have hind : MemLp (T.indicator (1 : Ω → ℝ)) 2 μ := (memLp_const 1).indicator hT.nullMeasurableSet
  have heL : MemLp e 2 μ := MemLp.of_bound he (max |ε| |1 - ε|) (heε.mono fun ω h => by
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs h.1 h.2)
  have ha : MemLp a 2 μ := (MemLp.condExp (m := m) (by norm_num) hind).sub heL
  have hb₁ : MemLp b₁ 2 μ := (MemLp.condExp (m := m) (by norm_num) hY₁).sub hg₁
  have hb₀ : MemLp b₀ 2 μ := (MemLp.condExp (m := m) (by norm_num) hY₀).sub hg₀
  have hi₁ : Integrable (fun ω => |a ω| * |b₁ ω|) μ := by
    simpa [abs_mul] using (ha.integrable_mul hb₁).abs
  have hi₀ : Integrable (fun ω => |a ω| * |b₀ ω|) μ := by
    simpa [abs_mul] using (ha.integrable_mul hb₀).abs
  calc |aipwRemainder μ m T Y₀ Y₁ e g₀ g₁|
      ≤ ∫ ω, |a ω * (b₁ ω / e ω + b₀ ω / (1 - e ω))| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, ε⁻¹ * (|a ω| * |b₁ ω| + |a ω| * |b₀ ω|) ∂μ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          ((hi₁.add hi₀).const_mul _) ?_
        filter_upwards [heε] with ω h
        have he0 : 0 < e ω := hε.trans_le h.1
        have he1 : 0 < 1 - e ω := by linarith [h.2]
        have hinv₁ : 1 / e ω ≤ ε⁻¹ := by rw [one_div]; exact inv_anti₀ hε h.1
        have hinv₀ : 1 / (1 - e ω) ≤ ε⁻¹ := by
          rw [one_div]; exact inv_anti₀ hε (by linarith [h.2])
        rw [abs_mul]
        calc |a ω| * |b₁ ω / e ω + b₀ ω / (1 - e ω)|
            ≤ |a ω| * (|b₁ ω| * (1 / e ω) + |b₀ ω| * (1 / (1 - e ω))) := by
              gcongr
              refine (abs_add_le _ _).trans_eq ?_
              rw [abs_div, abs_div, abs_of_pos he0, abs_of_pos he1]
              ring
          _ ≤ |a ω| * (|b₁ ω| * ε⁻¹ + |b₀ ω| * ε⁻¹) := by gcongr
          _ = ε⁻¹ * (|a ω| * |b₁ ω| + |a ω| * |b₀ ω|) := by ring
    _ = ε⁻¹ * (∫ ω, |a ω| * |b₁ ω| ∂μ + ∫ ω, |a ω| * |b₀ ω| ∂μ) := by
        rw [integral_const_mul, integral_add hi₁ hi₀]
    _ ≤ ε⁻¹ * (√(∫ ω, a ω ^ 2 ∂μ) * √(∫ ω, b₁ ω ^ 2 ∂μ) +
          √(∫ ω, a ω ^ 2 ∂μ) * √(∫ ω, b₀ ω ^ 2 ∂μ)) := by
        gcongr
        · exact integral_abs_mul_abs_le ha hb₁
        · exact integral_abs_mul_abs_le ha hb₀
    _ = _ := by ring

end Remainder

section PopulationCrossFit

variable {Ω Ωₜ : Type*} {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} [MeasurableSpace Ωₜ]
  {μ : Measure Ω} {μₜ : Measure Ωₜ} [IsProbabilityMeasure μ] [IsProbabilityMeasure μₜ]
  {T : Set Ω} {Y Y₀ Y₁ : Ω → ℝ}

/-- **Sample-split AIPW: the exact bias is the training-mean of the product remainder.**
The training sample is a point `ωₜ` of `(Ωₜ, μₜ)`, independent of the evaluation unit `ω`
(the joint law is `μₜ.prod μ`), and the fitted nuisances `ê ωₜ, ĝ₀ ωₜ, ĝ₁ ωₜ` depend on the
training sample only. For each training sample the fitted nuisances satisfy the hypotheses of
`integral_aipwScoreOfSigma_sub` (with an `ε` that may depend on `ωₜ`); `hint` is joint
integrability of the score, needed for Fubini. Then
`E[ψ(ê, ĝ₀, ĝ₁)] - E[Y₁ - Y₀] = E_train[aipwRemainder(ê, ĝ₀, ĝ₁)]`. -/
theorem integral_crossFit_sub (hm : m ≤ mΩ) (hT : MeasurableSet[mΩ] T)
    (hcons : Y =ᵐ[μ] observed T Y₀ Y₁) (hY₀ : Integrable Y₀ μ) (hY₁ : Integrable Y₁ μ)
    (hex₁ : μ[T.indicator Y₁ | m] =ᵐ[μ] μ[T.indicator 1 | m] * μ[Y₁ | m])
    (hex₀ : μ[Tᶜ.indicator Y₀ | m] =ᵐ[μ] (1 - μ[T.indicator 1 | m]) * μ[Y₀ | m])
    {ê ĝ₀ ĝ₁ : Ωₜ → Ω → ℝ} (he : ∀ ωₜ, StronglyMeasurable[m] (ê ωₜ))
    (hg₀ : ∀ ωₜ, StronglyMeasurable[m] (ĝ₀ ωₜ)) (hg₁ : ∀ ωₜ, StronglyMeasurable[m] (ĝ₁ ωₜ))
    (hg₀i : ∀ ωₜ, Integrable (ĝ₀ ωₜ) μ) (hg₁i : ∀ ωₜ, Integrable (ĝ₁ ωₜ) μ)
    (heε : ∀ ωₜ, ∃ ε, 0 < ε ∧ ∀ᵐ ω ∂μ, ε ≤ ê ωₜ ω ∧ ê ωₜ ω ≤ 1 - ε)
    (hint : Integrable (fun z : Ωₜ × Ω =>
      aipwScoreOfSigma T Y (ê z.1) (ĝ₀ z.1) (ĝ₁ z.1) z.2) (μₜ.prod μ)) :
    ∫ z, aipwScoreOfSigma T Y (ê z.1) (ĝ₀ z.1) (ĝ₁ z.1) z.2 ∂(μₜ.prod μ) -
        ∫ ω, (Y₁ ω - Y₀ ω) ∂μ =
      ∫ ωₜ, aipwRemainder μ m T Y₀ Y₁ (ê ωₜ) (ĝ₀ ωₜ) (ĝ₁ ωₜ) ∂μₜ := by
  have hfib : ∀ ωₜ, ∫ ω, aipwScoreOfSigma T Y (ê ωₜ) (ĝ₀ ωₜ) (ĝ₁ ωₜ) ω ∂μ =
      ∫ ω, (Y₁ ω - Y₀ ω) ∂μ + aipwRemainder μ m T Y₀ Y₁ (ê ωₜ) (ĝ₀ ωₜ) (ĝ₁ ωₜ) := by
    intro ωₜ
    obtain ⟨ε, hε, hb⟩ := heε ωₜ
    rw [aipwRemainder, ← integral_aipwScoreOfSigma_sub hm hT hcons hY₀ hY₁ hex₁ hex₀ (he ωₜ)
      (hg₀ ωₜ) (hg₁ ωₜ) (hg₀i ωₜ) (hg₁i ωₜ) hε hb]
    ring
  have hInner : Integrable (fun ωₜ => ∫ ω, aipwScoreOfSigma T Y (ê ωₜ) (ĝ₀ ωₜ) (ĝ₁ ωₜ) ω ∂μ)
      μₜ := hint.integral_prod_left
  have hRem : Integrable (fun ωₜ => aipwRemainder μ m T Y₀ Y₁ (ê ωₜ) (ĝ₀ ωₜ) (ĝ₁ ωₜ)) μₜ :=
    (hInner.sub (integrable_const (∫ ω, (Y₁ ω - Y₀ ω) ∂μ))).congr
      (Filter.Eventually.of_forall fun ωₜ => by simp only [Pi.sub_apply, hfib]; ring)
  rw [integral_prod _ hint]
  simp only [hfib]
  rw [integral_add (integrable_const _) hRem, integral_const, probReal_univ, one_smul]
  ring

/-- **Double robustness with sample-split nuisances.** Under the hypotheses of
`integral_crossFit_sub`, if for almost every training sample the fitted propensity is correct
*or* both fitted outcome regressions are correct, the sample-split AIPW score is unbiased for
the average treatment effect. Which nuisance is correct may vary with the training sample. -/
theorem integral_crossFit_eq (hm : m ≤ mΩ) (hT : MeasurableSet[mΩ] T)
    (hcons : Y =ᵐ[μ] observed T Y₀ Y₁) (hY₀ : Integrable Y₀ μ) (hY₁ : Integrable Y₁ μ)
    (hex₁ : μ[T.indicator Y₁ | m] =ᵐ[μ] μ[T.indicator 1 | m] * μ[Y₁ | m])
    (hex₀ : μ[Tᶜ.indicator Y₀ | m] =ᵐ[μ] (1 - μ[T.indicator 1 | m]) * μ[Y₀ | m])
    {ê ĝ₀ ĝ₁ : Ωₜ → Ω → ℝ} (he : ∀ ωₜ, StronglyMeasurable[m] (ê ωₜ))
    (hg₀ : ∀ ωₜ, StronglyMeasurable[m] (ĝ₀ ωₜ)) (hg₁ : ∀ ωₜ, StronglyMeasurable[m] (ĝ₁ ωₜ))
    (hg₀i : ∀ ωₜ, Integrable (ĝ₀ ωₜ) μ) (hg₁i : ∀ ωₜ, Integrable (ĝ₁ ωₜ) μ)
    (heε : ∀ ωₜ, ∃ ε, 0 < ε ∧ ∀ᵐ ω ∂μ, ε ≤ ê ωₜ ω ∧ ê ωₜ ω ≤ 1 - ε)
    (hint : Integrable (fun z : Ωₜ × Ω =>
      aipwScoreOfSigma T Y (ê z.1) (ĝ₀ z.1) (ĝ₁ z.1) z.2) (μₜ.prod μ))
    (hdr : ∀ᵐ ωₜ ∂μₜ, ê ωₜ =ᵐ[μ] μ[T.indicator 1 | m] ∨
      (ĝ₀ ωₜ =ᵐ[μ] μ[Y₀ | m] ∧ ĝ₁ ωₜ =ᵐ[μ] μ[Y₁ | m])) :
    ∫ z, aipwScoreOfSigma T Y (ê z.1) (ĝ₀ z.1) (ĝ₁ z.1) z.2 ∂(μₜ.prod μ) =
      ∫ ω, (Y₁ ω - Y₀ ω) ∂μ := by
  rw [← sub_eq_zero, integral_crossFit_sub hm hT hcons hY₀ hY₁ hex₁ hex₀ he hg₀ hg₁ hg₀i hg₁i
    heε hint, ← integral_zero Ωₜ ℝ]
  refine integral_congr_ae ?_
  filter_upwards [hdr] with ωₜ h
  rcases h with h | ⟨h₀, h₁⟩
  · exact aipwRemainder_eq_zero_of_propensity h
  · exact aipwRemainder_eq_zero_of_outcome h₀ h₁

end PopulationCrossFit

section SplitSample

open ProbabilityTheory

variable {Ω 𝒰 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒰] [MeasurableSpace 𝒲]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure 𝒲} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
/-- Independence turns the joint law into a product law. -/
private lemma map_pair_eq {U : Ω → 𝒰} {V : Ω → 𝒲} (hU : Measurable U) (hV : Measurable V)
    (hlaw : P.map V = ν) (hind : IndepFun U V P) :
    P.map (fun ω => (U ω, V ω)) = (P.map U).prod ν := by
  rw [← hlaw]
  exact (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).1 hind

omit [IsProbabilityMeasure ν] in
private lemma integral_comp_pair {U : Ω → 𝒰} {V : Ω → 𝒲} (hU : Measurable U)
    (hV : Measurable V) (hlaw : P.map V = ν) (hind : IndepFun U V P) {F : 𝒰 × 𝒲 → ℝ}
    (hF : StronglyMeasurable F) :
    ∫ ω, F (U ω, V ω) ∂P = ∫ z, F z ∂((P.map U).prod ν) := by
  rw [← map_pair_eq hU hV hlaw hind,
    integral_map (hU.prodMk hV).aemeasurable hF.aestronglyMeasurable]

omit [IsProbabilityMeasure ν] in
private lemma integrable_comp_pair_iff {U : Ω → 𝒰} {V : Ω → 𝒲} (hU : Measurable U)
    (hV : Measurable V) (hlaw : P.map V = ν) (hind : IndepFun U V P) {F : 𝒰 × 𝒲 → ℝ}
    (hF : StronglyMeasurable F) :
    Integrable (fun ω => F (U ω, V ω)) P ↔ Integrable F ((P.map U).prod ν) := by
  rw [← map_pair_eq hU hV hlaw hind,
    integrable_map_measure hF.aestronglyMeasurable (hU.prodMk hV).aemeasurable]
  rfl

/-- **The cross-fitting variance identity.** Let the training data `U` and the evaluation
units `V i`, `i ∈ s`, be such that each `V i` has law `ν` and is independent of `U`, and each
`V j` is independent of `(U, V i)` for `i ≠ j` (true when `U` and the `V i` are mutually
independent). For a kernel `D(u, w)` that is centered in `w` for every training value
(`∫ D(u, w) dν(w) = 0`) and square integrable under `law(U) ⊗ ν`,
`E[(∑_{i ∈ s} D(U, V i))²] = |s| E_{law(U) ⊗ ν}[D²]`.
The cross terms vanish because, given the training data, distinct evaluation units are
independent draws from `ν`; no entropy or Donsker condition on the class of kernels is used. -/
theorem integral_sq_sum_of_indep {ι : Type*} (s : Finset ι) {U : Ω → 𝒰} {V : ι → Ω → 𝒲}
    (hU : Measurable U) (hV : ∀ i, Measurable (V i)) (hlaw : ∀ i ∈ s, P.map (V i) = ν)
    (hind₁ : ∀ i ∈ s, IndepFun U (V i) P)
    (hind₂ : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IndepFun (fun ω => (U ω, V i ω)) (V j) P)
    {D : 𝒰 × 𝒲 → ℝ} (hD : StronglyMeasurable D) (hcent : ∀ u, ∫ w, D (u, w) ∂ν = 0)
    (hD2 : Integrable (fun z => D z ^ 2) ((P.map U).prod ν)) :
    ∫ ω, (∑ i ∈ s, D (U ω, V i ω)) ^ 2 ∂P = s.card * ∫ z, D z ^ 2 ∂((P.map U).prod ν) := by
  have hsq : ∀ i ∈ s, Integrable (fun ω => D (U ω, V i ω) ^ 2) P := fun i hi =>
    (integrable_comp_pair_iff hU (hV i) (hlaw i hi) (hind₁ i hi) (hD.pow 2)).2 hD2
  have hL2 : ∀ i ∈ s, MemLp (fun ω => D (U ω, V i ω)) 2 P := fun i hi =>
    (memLp_two_iff_integrable_sq
      (hD.comp_measurable (hU.prodMk (hV i))).aestronglyMeasurable).2 (hsq i hi)
  have hint : ∀ i ∈ s, ∀ j ∈ s, Integrable (fun ω => D (U ω, V i ω) * D (U ω, V j ω)) P :=
    fun i hi j hj => (hL2 i hi).integrable_mul (hL2 j hj)
  have hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∫ ω, D (U ω, V i ω) * D (U ω, V j ω) ∂P = 0 := by
    intro i hi j hj hij
    set G : (𝒰 × 𝒲) × 𝒲 → ℝ := fun p => D p.1 * D (p.1.1, p.2) with hGdef
    have hG : StronglyMeasurable G :=
      (hD.comp_measurable measurable_fst).mul
        (hD.comp_measurable (measurable_fst.fst.prodMk measurable_snd))
    have hUV : Measurable fun ω => (U ω, V i ω) := hU.prodMk (hV i)
    have hmap := map_pair_eq hUV (hV j) (hlaw j hj) (hind₂ i hi j hj hij)
    rw [map_pair_eq hU (hV i) (hlaw i hi) (hind₁ i hi)] at hmap
    have hGi : Integrable G (((P.map U).prod ν).prod ν) := by
      rw [← hmap, integrable_map_measure hG.aestronglyMeasurable (hUV.prodMk (hV j)).aemeasurable]
      exact hint i hi j hj
    calc ∫ ω, D (U ω, V i ω) * D (U ω, V j ω) ∂P = ∫ p, G p ∂(((P.map U).prod ν).prod ν) := by
          rw [← hmap, integral_map (hUV.prodMk (hV j)).aemeasurable hG.aestronglyMeasurable]
      _ = ∫ z, ∫ w, G (z, w) ∂ν ∂((P.map U).prod ν) := integral_prod G hGi
      _ = 0 := by simp [G, integral_const_mul, hcent]
  have hdiag : ∀ i ∈ s, ∫ ω, D (U ω, V i ω) * D (U ω, V i ω) ∂P =
      ∫ z, D z ^ 2 ∂((P.map U).prod ν) := by
    intro i hi
    rw [← integral_comp_pair hU (hV i) (hlaw i hi) (hind₁ i hi) (F := fun z => D z ^ 2) (hD.pow 2)]
    simp [sq]
  classical
  calc ∫ ω, (∑ i ∈ s, D (U ω, V i ω)) ^ 2 ∂P
      = ∫ ω, ∑ i ∈ s, ∑ j ∈ s, D (U ω, V i ω) * D (U ω, V j ω) ∂P := by
        simp_rw [sq, Finset.sum_mul_sum]
    _ = ∑ i ∈ s, ∑ j ∈ s, ∫ ω, D (U ω, V i ω) * D (U ω, V j ω) ∂P := by
        rw [integral_finsetSum _ fun i hi => integrable_finsetSum _ fun j hj => hint i hi j hj]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [integral_finsetSum _ fun j hj => hint i hi j hj]
    _ = ∑ i ∈ s, ∫ z, D z ^ 2 ∂((P.map U).prod ν) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.sum_eq_single i (fun j hj hji => hoff i hi j hj (Ne.symm hji))
          (fun h => absurd hi h), hdiag i hi]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Centering a square-integrable function does not increase its second moment. -/
private lemma integral_sub_integral_sq_le {f : 𝒲 → ℝ} (hf : MemLp f 2 ν) :
    ∫ w, (f w - ∫ w', f w' ∂ν) ^ 2 ∂ν ≤ ∫ w, f w ^ 2 ∂ν := by
  rw [← variance_eq_integral hf.aestronglyMeasurable.aemeasurable]
  exact variance_le_expectation_sq hf.aestronglyMeasurable

/-- **Conditional Chebyshev bound for a split-sample empirical process term**, at a fixed
sample size. With `r(u) = ∫ Δ(u, w)² dν(w)` the conditional `L²` error of the kernel given the
training value and `|s| ≤ c`, for every `δ, η > 0`,
`P(δ ≤ |c^{-1/2} ∑_{i ∈ s} (Δ(U, V i) - ∫ Δ(U, w) dν(w))|) ≤ P(η ≤ r(U)) + η / δ²`.
The proof truncates the kernel to training values with `r(u) < η` and applies
`integral_sq_sum_of_indep` to the truncated, centered kernel. -/
theorem measureReal_le_of_indep {ι : Type*} (s : Finset ι) {c : ℝ} (hc : (s.card : ℝ) ≤ c)
    {U : Ω → 𝒰} {V : ι → Ω → 𝒲} (hU : Measurable U) (hV : ∀ i, Measurable (V i))
    (hlaw : ∀ i ∈ s, P.map (V i) = ν) (hind₁ : ∀ i ∈ s, IndepFun U (V i) P)
    (hind₂ : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IndepFun (fun ω => (U ω, V i ω)) (V j) P)
    {Δ : 𝒰 × 𝒲 → ℝ} (hΔ : StronglyMeasurable Δ) (hΔ2 : ∀ u, MemLp (fun w => Δ (u, w)) 2 ν)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    P.real {ω | δ ≤ |(√c)⁻¹ * ∑ i ∈ s, (Δ (U ω, V i ω) - ∫ w, Δ (U ω, w) ∂ν)|} ≤
      P.real {ω | η ≤ ∫ w, Δ (U ω, w) ^ 2 ∂ν} + η / δ ^ 2 := by
  set r : 𝒰 → ℝ := fun u => ∫ w, Δ (u, w) ^ 2 ∂ν with hr_def
  set β : 𝒰 → ℝ := fun u => ∫ w, Δ (u, w) ∂ν with hβ_def
  have hr : StronglyMeasurable r := (hΔ.pow 2).integral_prod_right'
  have hβ : StronglyMeasurable β := hΔ.integral_prod_right'
  have hrset : MeasurableSet {z : 𝒰 × 𝒲 | r z.1 < η} :=
    measurableSet_lt (hr.measurable.comp measurable_fst) measurable_const
  classical
  set D : 𝒰 × 𝒲 → ℝ := fun z => if r z.1 < η then Δ z - β z.1 else 0 with hD_def
  have hD : StronglyMeasurable D :=
    StronglyMeasurable.ite hrset (hΔ.sub (hβ.comp_measurable measurable_fst))
      stronglyMeasurable_const
  have hcL2 : ∀ u, MemLp (fun w => Δ (u, w) - β u) 2 ν := fun u => (hΔ2 u).sub (memLp_const _)
  have hcent : ∀ u, ∫ w, D (u, w) ∂ν = 0 := by
    intro u
    by_cases hu : r u < η
    · simp only [hD_def, hu, ite_true]
      rw [integral_sub ((hΔ2 u).integrable (by norm_num)) (integrable_const _), integral_const,
        probReal_univ, one_smul, sub_self]
    · simp [hD_def, hu]
  have hfib : ∀ u, ∫ w, D (u, w) ^ 2 ∂ν ≤ if r u < η then r u else 0 := by
    intro u
    by_cases hu : r u < η
    · simp only [hD_def, hu, ite_true]
      exact integral_sub_integral_sq_le (hΔ2 u)
    · simp [hD_def, hu]
  have hfib_le : ∀ u, ∫ w, D (u, w) ^ 2 ∂ν ≤ η := fun u => (hfib u).trans (by
    split_ifs with hu
    · exact hu.le
    · exact hη.le)
  have hfib_nn : ∀ u, 0 ≤ ∫ w, D (u, w) ^ 2 ∂ν := fun u =>
    integral_nonneg fun _ => sq_nonneg _
  have hD2 : Integrable (fun z => D z ^ 2) ((P.map U).prod ν) := by
    refine (integrable_prod_iff (hD.pow 2).aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall
      fun u => ?_, ?_⟩
    · by_cases hu : r u < η
      · simpa [hD_def, hu] using (hcL2 u).integrable_sq
      · simp [hD_def, hu]
    · refine Integrable.of_bound ((hD.pow 2).norm.integral_prod_right').aestronglyMeasurable η
        (Filter.Eventually.of_forall fun u => ?_)
      have h' : ∫ w, ‖D (u, w) ^ 2‖ ∂ν = ∫ w, D (u, w) ^ 2 ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall fun w => by
          change ‖D (u, w) ^ 2‖ = D (u, w) ^ 2
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (D (u, w)))])
      change ‖∫ w, ‖D (u, w) ^ 2‖ ∂ν‖ ≤ η
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), h']
      exact hfib_le u
  have hE : ∫ z, D z ^ 2 ∂((P.map U).prod ν) ≤ η := by
    rw [integral_prod _ hD2]
    calc ∫ u, ∫ w, D (u, w) ^ 2 ∂ν ∂(P.map U) ≤ ∫ _u, η ∂(P.map U) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall hfib_nn) (integrable_const _)
            (Filter.Eventually.of_forall hfib_le)
      _ = η := by
          rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
  -- the truncated statistic
  set A : Ω → ℝ := fun ω => (√c)⁻¹ * ∑ i ∈ s, (Δ (U ω, V i ω) - β (U ω)) with hA_def
  set B : Ω → ℝ := fun ω => (√c)⁻¹ * ∑ i ∈ s, D (U ω, V i ω) with hB_def
  have hDL2 : ∀ i ∈ s, MemLp (fun ω => D (U ω, V i ω)) 2 P := fun i hi =>
    (memLp_two_iff_integrable_sq (hD.comp_measurable (hU.prodMk (hV i))).aestronglyMeasurable).2
      ((integrable_comp_pair_iff hU (hV i) (hlaw i hi) (hind₁ i hi)
        (F := fun z => D z ^ 2) (hD.pow 2)).2 hD2)
  have hBL2 : MemLp B 2 P := by
    have : MemLp (fun ω => ∑ i ∈ s, D (U ω, V i ω)) 2 P := by
      exact memLp_finsetSum s hDL2
    exact this.const_mul _
  have hEB : ∫ ω, B ω ^ 2 ∂P ≤ η := by
    have hsum := integral_sq_sum_of_indep s hU hV hlaw hind₁ hind₂ hD hcent hD2
    have hB2 : (fun ω => B ω ^ 2) = fun ω => (√c)⁻¹ ^ 2 * (∑ i ∈ s, D (U ω, V i ω)) ^ 2 := by
      funext ω; simp only [hB_def]; ring
    rw [hB2, integral_const_mul, hsum]
    rcases le_or_gt c 0 with hc0 | hc0
    · rw [Real.sqrt_eq_zero'.2 hc0, inv_zero]
      simpa using hη.le
    · have hEn : 0 ≤ ∫ z, D z ^ 2 ∂((P.map U).prod ν) := integral_nonneg fun _ => sq_nonneg _
      rw [inv_pow, Real.sq_sqrt hc0.le]
      calc c⁻¹ * (s.card * ∫ z, D z ^ 2 ∂((P.map U).prod ν))
          ≤ c⁻¹ * (c * ∫ z, D z ^ 2 ∂((P.map U).prod ν)) := by gcongr
        _ = ∫ z, D z ^ 2 ∂((P.map U).prod ν) := by field_simp
        _ ≤ η := hE
  have hcheb : P.real {ω | δ ≤ |B ω|} ≤ η / δ ^ 2 := by
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P)
      (Filter.Eventually.of_forall fun ω => sq_nonneg (B ω)) hBL2.integrable_sq (δ ^ 2)
    have hsub : {ω | δ ≤ |B ω|} ⊆ {ω | δ ^ 2 ≤ B ω ^ 2} := fun ω hω => by
      simp only [Set.mem_ofPred_eq] at hω ⊢
      calc δ ^ 2 ≤ |B ω| ^ 2 := pow_le_pow_left₀ hδ.le hω 2
        _ = B ω ^ 2 := sq_abs _
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact ((mul_le_mul_of_nonneg_left (measureReal_mono hsub) (by positivity))).trans
      (hmk.trans hEB)
  have hsplit : {ω | δ ≤ |A ω|} ⊆ {ω | η ≤ r (U ω)} ∪ {ω | δ ≤ |B ω|} := by
    intro ω hω
    by_cases hu : r (U ω) < η
    · right
      have hAB : A ω = B ω := by
        simp only [hA_def, hB_def, hD_def, hu, ite_true]
      simpa [hAB] using hω
    · left
      exact not_lt.1 hu
  exact (measureReal_mono hsplit).trans ((measureReal_union_le _ _).trans
    (add_le_add le_rfl hcheb))

end SplitSample

section Asymptotic

open ProbabilityTheory Filter Topology

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure 𝒲} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure P] in
/-- A sum of two sequences tending to `0` in probability tends to `0` in probability. -/
private lemma tendstoInMeasure_add_zero {f g : ℕ → Ω → ℝ} (hf : TendstoInMeasure P f atTop 0)
    (hg : TendstoInMeasure P g atTop 0) :
    TendstoInMeasure P (fun n ω => f n ω + g n ω) atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  intro ε hε
  have h2 := (hf (ε / 2) (by positivity)).add (hg (ε / 2) (by positivity))
  rw [add_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => zero_le)
    fun n => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω ⊢
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at h
  linarith [abs_add_le (f n ω) (g n ω)]

omit [IsProbabilityMeasure P] in
/-- A finite sum of sequences tending to `0` in probability tends to `0` in probability. -/
private lemma tendstoInMeasure_finsetSum_zero {κ : Type*} (t : Finset κ) {f : κ → ℕ → Ω → ℝ}
    (hf : ∀ k ∈ t, TendstoInMeasure P (f k) atTop 0) :
    TendstoInMeasure P (fun n ω => ∑ k ∈ t, f k n ω) atTop 0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    intro ε hε
    simp [not_le.2 hε]
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact tendstoInMeasure_add_zero (hf a (Finset.mem_insert_self a t))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

omit [IsProbabilityMeasure P] in
/-- Domination by a sequence tending to `0` in probability. -/
private lemma tendstoInMeasure_zero_of_abs_le {f g : ℕ → Ω → ℝ}
    (hg : TendstoInMeasure P g atTop 0) (hfg : ∀ n ω, |f n ω| ≤ |g n ω|) :
    TendstoInMeasure P f atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hg ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg ε hε)
    (fun _ => zero_le) fun n => measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω ⊢
  exact hω.trans (hfg n ω)

/-- **Cross-fitting removes the Donsker condition.** Along a sequence of sample sizes, let
`U n` be the training data (in a type `𝒰 n` that may depend on `n`), `s n` the evaluation
indices, and `Δ n (u, w)` a kernel, for example the difference between the score at the
nuisances fitted on training data `u` and the score at the true nuisances. Under the
independence structure of `integral_sq_sum_of_indep`, if the conditional `L²` error
`∫ Δ n (U n, w)² dν(w)` tends to `0` in probability, then the centered split-sample empirical
process term `c_n^{-1/2} ∑_{i ∈ s n} (Δ n (U n, V i) - ∫ Δ n (U n, w) dν(w))`, with
`|s n| ≤ c n`, tends to `0` in probability. No complexity (entropy, Donsker) condition on the
class of fitted kernels is assumed. -/
theorem tendstoInMeasure_crossFit_empirical {ι : Type*} {𝒰 : ℕ → Type*}
    [∀ n, MeasurableSpace (𝒰 n)] (s : ℕ → Finset ι) (c : ℕ → ℝ)
    (hc : ∀ n, ((s n).card : ℝ) ≤ c n) {U : (n : ℕ) → Ω → 𝒰 n} {V : ι → Ω → 𝒲}
    (hU : ∀ n, Measurable (U n)) (hV : ∀ i, Measurable (V i))
    (hlaw : ∀ n, ∀ i ∈ s n, P.map (V i) = ν) (hind₁ : ∀ n, ∀ i ∈ s n, IndepFun (U n) (V i) P)
    (hind₂ : ∀ n, ∀ i ∈ s n, ∀ j ∈ s n, i ≠ j → IndepFun (fun ω => (U n ω, V i ω)) (V j) P)
    {Δ : (n : ℕ) → 𝒰 n × 𝒲 → ℝ} (hΔ : ∀ n, StronglyMeasurable (Δ n))
    (hΔ2 : ∀ n u, MemLp (fun w => Δ n (u, w)) 2 ν)
    (hr : TendstoInMeasure P (fun n ω => ∫ w, Δ n (U n ω, w) ^ 2 ∂ν) atTop 0) :
    TendstoInMeasure P (fun n ω => (√(c n))⁻¹ * ∑ i ∈ s n,
      (Δ n (U n ω, V i ω) - ∫ w, Δ n (U n ω, w) ∂ν)) atTop 0 := by
  rw [tendstoInMeasure_iff_measureReal_norm] at hr ⊢
  intro δ hδ
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n =>
    ha.trans_le measureReal_nonneg, fun a ha => ?_⟩
  set η := a * δ ^ 2 / 2 with hη_def
  have hη : 0 < η := by positivity
  have h1 := (tendsto_order.1 (hr η hη)).2 (a / 2) (by positivity)
  filter_upwards [h1] with n hn
  have hb := measureReal_le_of_indep (s n) (hc n) (hU n) hV (hlaw n) (hind₁ n) (hind₂ n)
    (hΔ n) (hΔ2 n) hδ hη
  simp only [Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hn ⊢
  have hset : {ω | η ≤ |∫ w, Δ n (U n ω, w) ^ 2 ∂ν|} = {ω | η ≤ ∫ w, Δ n (U n ω, w) ^ 2 ∂ν} := by
    ext ω
    have h0 : 0 ≤ ∫ w, Δ n (U n ω, w) ^ 2 ∂ν := integral_nonneg fun w => sq_nonneg (Δ n (U n ω, w))
    simp only [Set.mem_ofPred_eq, abs_of_nonneg h0]
  rw [hset] at hn
  calc _ ≤ _ := hb
    _ < a / 2 + η / δ ^ 2 := by linarith
    _ = a := by rw [hη_def]; field_simp; ring

/-- The evaluation indices of fold `k` at sample size `n`: the units `i < n` that the fold
assignment `fold n` puts in fold `k`. -/
def evalFold {K : ℕ} (fold : ℕ → ℕ → Fin K) (n : ℕ) (k : Fin K) : Finset ℕ :=
  (Finset.range n).filter fun i => fold n i = k

/-- The training indices for fold `k` at sample size `n`: the units `i < n` outside fold `k`. -/
def trainFold {K : ℕ} (fold : ℕ → ℕ → Fin K) (n : ℕ) (k : Fin K) : Finset ℕ :=
  (Finset.range n).filter fun i => fold n i ≠ k

/-- The training data for fold `k` at sample size `n`: the observations `W i` of the units
`i ∈ trainFold fold n k`. Nuisances for fold `k` are fitted on these only. -/
def trainData {K : ℕ} (W : ℕ → Ω → 𝒲) (fold : ℕ → ℕ → Fin K) (n : ℕ) (k : Fin K) :
    Ω → (trainFold fold n k → 𝒲) :=
  fun ω i => W i ω

/-- The **cross-fitted estimator**. `G n k (u, w)` is the score of an observation `w` at the
nuisances fitted on training data `u` of fold `k` (for AIPW,
`G n k (u, ·) = aipwScoreOfSigma T Y (ê u) (ĝ₀ u) (ĝ₁ u)`). Each unit `i < n` is scored with
the nuisances fitted on the training data of its own fold, which excludes it, and the
estimator averages: `θ̂ₙ = n⁻¹ ∑_{i < n} G n (fold n i) (trainData (fold n i), W i)`. -/
noncomputable def crossFitEstimator {K : ℕ} (W : ℕ → Ω → 𝒲) (fold : ℕ → ℕ → Fin K)
    (G : (n : ℕ) → (k : Fin K) → (trainFold fold n k → 𝒲) × 𝒲 → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, G n (fold n i) (trainData W fold n (fold n i) ω, W i ω)

omit [MeasurableSpace 𝒲] in
/-- Membership in an evaluation fold. -/
lemma mem_evalFold {K : ℕ} {fold : ℕ → ℕ → Fin K} {n i : ℕ} {k : Fin K} :
    i ∈ evalFold fold n k ↔ i < n ∧ fold n i = k := by
  simp [evalFold]

omit [MeasurableSpace 𝒲] in
/-- Membership in a training fold. -/
lemma mem_trainFold {K : ℕ} {fold : ℕ → ℕ → Fin K} {n i : ℕ} {k : Fin K} :
    i ∈ trainFold fold n k ↔ i < n ∧ fold n i ≠ k := by
  simp [trainFold]

omit [IsProbabilityMeasure P] in
private lemma measurable_trainData {K : ℕ} {W : ℕ → Ω → 𝒲} (hW : ∀ i, Measurable (W i))
    (fold : ℕ → ℕ → Fin K) (n : ℕ) (k : Fin K) : Measurable (trainData W fold n k) :=
  Measurable.of_eval fun j => hW j

omit [IsProbabilityMeasure P] in
/-- An evaluation unit of fold `k` is independent of the training data of fold `k`. -/
private lemma indepFun_trainData {K : ℕ} {W : ℕ → Ω → 𝒲} (hW : ∀ i, Measurable (W i))
    (hindep : iIndepFun W P) (fold : ℕ → ℕ → Fin K) (n : ℕ) (k : Fin K) {i : ℕ}
    (hi : i ∈ evalFold fold n k) : IndepFun (trainData W fold n k) (W i) P := by
  have hdisj : Disjoint (trainFold fold n k) {i} := by
    rw [Finset.disjoint_singleton_right, mem_trainFold]
    exact fun h => h.2 (mem_evalFold.1 hi).2
  exact (hindep.indepFun_finset (trainFold fold n k) {i} hdisj hW).comp measurable_id
    (measurable_pi_apply (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset ℕ)))

omit [IsProbabilityMeasure P] in
/-- Two distinct evaluation units of fold `k`: the second is independent of the pair formed by
the training data and the first. -/
private lemma indepFun_trainData_pair {K : ℕ} {W : ℕ → Ω → 𝒲} (hW : ∀ i, Measurable (W i))
    (hindep : iIndepFun W P) (fold : ℕ → ℕ → Fin K) (n : ℕ) (k : Fin K) {i j : ℕ}
    (hj : j ∈ evalFold fold n k) (hij : i ≠ j) :
    IndepFun (fun ω => (trainData W fold n k ω, W i ω)) (W j) P := by
  classical
  have hdisj : Disjoint (insert i (trainFold fold n k)) {j} := by
    rw [Finset.disjoint_singleton_right, Finset.mem_insert, not_or, mem_trainFold]
    exact ⟨Ne.symm hij, fun h => h.2 (mem_evalFold.1 hj).2⟩
  have hφ : Measurable fun x : (insert i (trainFold fold n k) : Finset ℕ) → 𝒲 =>
      ((fun t : trainFold fold n k => x ⟨t, Finset.mem_insert_of_mem t.2⟩),
        x ⟨i, Finset.mem_insert_self i _⟩) :=
    (Measurable.of_eval fun t => measurable_pi_apply _).prodMk (measurable_pi_apply _)
  exact (hindep.indepFun_finset _ {j} hdisj hW).comp hφ
    (measurable_pi_apply (⟨j, Finset.mem_singleton_self j⟩ : ({j} : Finset ℕ)))

omit [MeasurableSpace 𝒲] in
/-- The cross-fitted estimator minus the oracle CLT statistic, split fold by fold into a
centered split-sample empirical process term and a bias term (for an arbitrary `β`). -/
private lemma crossFit_decomp {K : ℕ} (W : ℕ → Ω → 𝒲) (fold : ℕ → ℕ → Fin K)
    (G : (n : ℕ) → (k : Fin K) → (trainFold fold n k → 𝒲) × 𝒲 → ℝ) (ψ : 𝒲 → ℝ) (θ : ℝ)
    (β : (n : ℕ) → (k : Fin K) → (trainFold fold n k → 𝒲) → ℝ) (n : ℕ) (ω : Ω) :
    √n * (crossFitEstimator W fold G n ω - θ) -
        (√n)⁻¹ * (∑ i ∈ Finset.range n, ψ (W i ω) - n * θ) =
      ∑ k, ((√n)⁻¹ * ∑ i ∈ evalFold fold n k,
          ((G n k (trainData W fold n k ω, W i ω) - ψ (W i ω)) - β n k (trainData W fold n k ω)) +
        (√n)⁻¹ * ((evalFold fold n k).card * β n k (trainData W fold n k ω))) := by
  have ha : √(n : ℝ) * (n : ℝ)⁻¹ = (√n)⁻¹ := by rw [← div_eq_mul_inv, Real.sqrt_div_self]
  have hb : (√(n : ℝ))⁻¹ * n = √n := by rw [mul_comm, ← div_eq_mul_inv, Real.div_sqrt]
  have h3 : ∑ i ∈ Finset.range n, (G n (fold n i) (trainData W fold n (fold n i) ω, W i ω) -
      ψ (W i ω)) = ∑ k, ∑ i ∈ evalFold fold n k,
        (G n k (trainData W fold n k ω, W i ω) - ψ (W i ω)) := by
    rw [← Finset.sum_fiberwise (Finset.range n) (fold n)]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i hi => ?_
    obtain rfl := (Finset.mem_filter.1 hi).2
    rfl
  calc √n * (crossFitEstimator W fold G n ω - θ) -
        (√n)⁻¹ * (∑ i ∈ Finset.range n, ψ (W i ω) - n * θ)
      = (√n * (n : ℝ)⁻¹) * ∑ i ∈ Finset.range n,
            G n (fold n i) (trainData W fold n (fold n i) ω, W i ω) -
          (√n)⁻¹ * ∑ i ∈ Finset.range n, ψ (W i ω) - (√n - (√n)⁻¹ * n) * θ := by
        rw [crossFitEstimator]; ring
    _ = (√n)⁻¹ * ∑ i ∈ Finset.range n,
          (G n (fold n i) (trainData W fold n (fold n i) ω, W i ω) - ψ (W i ω)) := by
        rw [ha, hb, Finset.sum_sub_distrib]; ring
    _ = _ := by
        rw [h3, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        ring

/-- `√n (θ̂ - θ) - n^{-1/2} (∑ ψᵢ - n θ) = √n (θ̂ - n⁻¹ ∑ ψᵢ)`, also at `n = 0`. -/
private lemma sqrt_mul_sub_sub_eq (n : ℕ) (a b θ : ℝ) :
    √(n : ℝ) * (a - θ) - (√(n : ℝ))⁻¹ * (b - n * θ) = √(n : ℝ) * (a - (n : ℝ)⁻¹ * b) := by
  have ha : √(n : ℝ) * (n : ℝ)⁻¹ = (√n)⁻¹ := by rw [← div_eq_mul_inv, Real.sqrt_div_self]
  have hb : (√(n : ℝ))⁻¹ * n = √n := by rw [mul_comm, ← div_eq_mul_inv, Real.div_sqrt]
  calc √(n : ℝ) * (a - θ) - (√(n : ℝ))⁻¹ * (b - n * θ)
      = √(n : ℝ) * a - (√(n : ℝ))⁻¹ * b - (√(n : ℝ) - (√(n : ℝ))⁻¹ * n) * θ := by ring
    _ = √(n : ℝ) * (a - (n : ℝ)⁻¹ * b) := by rw [hb, ← ha]; ring

/-- **The cross-fitted estimator is `√n`-equivalent to the oracle estimator.** Let
`W 0, W 1, …` be i.i.d. with law `ν`, `ψ` the square-integrable score at the true nuisances,
and `G n k (u, ·)` the score at the nuisances fitted on the training data `u` of fold `k`
(square integrable for every `u`). Assume, for every fold:
* `L²` consistency of the fitted score: `∫ (G n k (Uₙₖ, w) - ψ w)² dν(w) → 0` in probability;
* vanishing bias at the `√n` rate: `√n (∫ G n k (Uₙₖ, w) dν(w) - ∫ ψ dν) → 0` in probability.
Then `√n (θ̂ₙ - θ̂ₙ*) → 0` in probability, where `θ̂ₙ* = n⁻¹ ∑_{i < n} ψ(W i)` is the oracle
estimator with the true nuisances. Because the nuisances of each fold are fitted on the other
folds, the empirical process term is controlled by `tendstoInMeasure_crossFit_empirical`
without any Donsker or entropy condition on the fitted scores.

This is the remainder statement `√n (τ̂ - τ̂*) → 0` in probability that an asymptotic-normality
argument for the oracle AIPW estimator takes as its hypothesis (`hrem` in the T143 AIPW
asymptotic-normality development): with `G` the AIPW score at fitted nuisances and `ψ` the AIPW
score at the true nuisances, `θ̂ₙ*` is the oracle AIPW estimator, and
`tendstoInMeasure_crossFit_aipw_sub_oracle` discharges the bias condition from product rates. -/
theorem tendstoInMeasure_crossFitEstimator_sub_oracle {W : ℕ → Ω → 𝒲}
    (hW : ∀ i, Measurable (W i)) (hindep : iIndepFun W P)
    (hident : ∀ i, IdentDistrib (W i) (W 0) P P) (hν : P.map (W 0) = ν) {ψ : 𝒲 → ℝ}
    (hψ : Measurable ψ) (hψ2 : MemLp ψ 2 ν) {K : ℕ} (fold : ℕ → ℕ → Fin K)
    {G : (n : ℕ) → (k : Fin K) → (trainFold fold n k → 𝒲) × 𝒲 → ℝ}
    (hG : ∀ n k, StronglyMeasurable (G n k)) (hG2 : ∀ n k u, MemLp (fun w => G n k (u, w)) 2 ν)
    (hcons : ∀ k, TendstoInMeasure P
      (fun n ω => ∫ w, (G n k (trainData W fold n k ω, w) - ψ w) ^ 2 ∂ν) atTop 0)
    (hbias : ∀ k, TendstoInMeasure P
      (fun (n : ℕ) ω => √(n : ℝ) * (∫ w, G n k (trainData W fold n k ω, w) ∂ν - ∫ w, ψ w ∂ν))
      atTop 0) :
    TendstoInMeasure P (fun (n : ℕ) ω => √(n : ℝ) *
      (crossFitEstimator W fold G n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ψ (W i ω)))
      atTop 0 := by
  set θ := ∫ w, ψ w ∂ν with hθ
  set β : (n : ℕ) → (k : Fin K) → (trainFold fold n k → 𝒲) → ℝ :=
    fun n k u => ∫ w, (G n k (u, w) - ψ w) ∂ν with hβ
  have hβθ : ∀ n k u, β n k u = ∫ w, G n k (u, w) ∂ν - θ := fun n k u => by
    change ∫ w, (G n k (u, w) - ψ w) ∂ν = _
    rw [integral_sub ((hG2 n k u).integrable (by norm_num)) (hψ2.integrable (by norm_num))]
  have hcard : ∀ n k, ((evalFold fold n k).card : ℝ) ≤ n := fun n k => by
    exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range n).le
  have hemp : ∀ k, TendstoInMeasure P (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ * ∑ i ∈ evalFold fold n k,
      ((G n k (trainData W fold n k ω, W i ω) - ψ (W i ω)) - β n k (trainData W fold n k ω)))
      atTop 0 := fun k =>
    tendstoInMeasure_crossFit_empirical (fun n => evalFold fold n k) (fun n => (n : ℝ))
      (fun n => hcard n k) (fun n => measurable_trainData hW fold n k) hW
      (fun n i _ => (hident i).map_eq.trans hν)
      (fun n i hi => indepFun_trainData hW hindep fold n k hi)
      (fun n i _ j hj hij => indepFun_trainData_pair hW hindep fold n k hj hij)
      (Δ := fun n z => G n k z - ψ z.2)
      (fun n => (hG n k).sub (hψ.comp measurable_snd).stronglyMeasurable)
      (fun n u => (hG2 n k u).sub hψ2) (hcons k)
  have hbias' : ∀ k, TendstoInMeasure P (fun (n : ℕ) ω => (√(n : ℝ))⁻¹ *
      ((evalFold fold n k).card * β n k (trainData W fold n k ω))) atTop 0 := by
    intro k
    refine tendstoInMeasure_zero_of_abs_le (hbias k) fun n ω => ?_
    rw [hβθ]
    have hcoef : (√(n : ℝ))⁻¹ * (evalFold fold n k).card ≤ √n := by
      calc (√(n : ℝ))⁻¹ * (evalFold fold n k).card ≤ (√(n : ℝ))⁻¹ * n := by
            gcongr; exact_mod_cast hcard n k
        _ = √n := by rw [mul_comm, ← div_eq_mul_inv, Real.div_sqrt]
    rw [← mul_assoc, abs_mul, abs_mul (√(n : ℝ)), abs_of_nonneg (by positivity),
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
  have hrem := tendstoInMeasure_finsetSum_zero Finset.univ
    (fun k _ => tendstoInMeasure_add_zero (hemp k) (hbias' k))
  convert hrem using 2 with n
  funext ω
  rw [← crossFit_decomp W fold G ψ θ β n ω, sqrt_mul_sub_sub_eq]

omit [IsProbabilityMeasure ν] in
/-- **From the oracle gap to asymptotic normality.** If `W 0, W 1, …` are i.i.d. with law `ν`,
`ψ` is square integrable, and an estimator satisfies `√n (θ̂ₙ - n⁻¹ ∑_{i < n} ψ(W i)) → 0` in
probability, then `√n (θ̂ₙ - ∫ ψ dν)` converges in distribution to `N(0, Var_ν ψ)`: the central
limit theorem for the oracle estimator plus Slutsky's lemma. -/
theorem tendstoInDistribution_of_tendstoInMeasure_oracle_gap {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {W : ℕ → Ω → 𝒲}
    (hW : ∀ i, Measurable (W i)) (hindep : iIndepFun W P)
    (hident : ∀ i, IdentDistrib (W i) (W 0) P P) (hν : P.map (W 0) = ν) {ψ : 𝒲 → ℝ}
    (hψ : Measurable ψ) (hψ2 : MemLp ψ 2 ν) {est : ℕ → Ω → ℝ} (hest : ∀ n, AEMeasurable (est n) P)
    (hgap : TendstoInMeasure P (fun (n : ℕ) ω => √(n : ℝ) *
      (est n ω - (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ψ (W i ω))) atTop 0)
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 Var[ψ; ν].toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) * (est n ω - ∫ w, ψ w ∂ν))
      atTop Z (fun _ => P) P' := by
  set θ := ∫ w, ψ w ∂ν with hθ
  set X : ℕ → Ω → ℝ := fun i ω => ψ (W i ω) with hX
  have hX2 : MemLp (X 0) 2 P := by
    have h := hψ2
    rw [← hν, memLp_map_measure_iff hψ.aestronglyMeasurable (hW 0).aemeasurable] at h
    exact h
  have hXind : iIndepFun X P := hindep.comp (fun _ => ψ) fun _ => hψ
  have hXid : ∀ i, IdentDistrib (X i) (X 0) P P := fun i => (hident i).comp hψ
  have hvar : Var[X 0; P] = Var[ψ; ν] := by
    rw [← hν, variance_map hψ.aemeasurable (hW 0).aemeasurable]
    rfl
  have hmean : P[X 0] = θ := by
    rw [hθ, ← hν, integral_map (hW 0).aemeasurable hψ.aestronglyMeasurable]
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub (hvar ▸ hZ) hX2 hXind hXid
  rw [hmean] at hclt
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ Z hclt ?_
    fun n => ((hest n).sub_const θ).const_mul _
  convert hgap using 2 with n
  funext ω
  simp only [Pi.sub_apply]
  exact sqrt_mul_sub_sub_eq n _ _ θ

omit [IsProbabilityMeasure P] in
private lemma measurable_crossFitEstimator {W : ℕ → Ω → 𝒲} (hW : ∀ i, Measurable (W i))
    {K : ℕ} (fold : ℕ → ℕ → Fin K)
    {G : (n : ℕ) → (k : Fin K) → (trainFold fold n k → 𝒲) × 𝒲 → ℝ}
    (hG : ∀ n k, StronglyMeasurable (G n k)) (n : ℕ) :
    Measurable fun ω => crossFitEstimator W fold G n ω :=
  (Finset.measurable_sum _ fun i _ => (hG n (fold n i)).measurable.comp
    ((measurable_trainData hW fold n (fold n i)).prodMk (hW i))).const_mul _

/-- **Asymptotic normality of a cross-fitted estimator** (double/debiased machine learning).
Under the hypotheses of `tendstoInMeasure_crossFitEstimator_sub_oracle` (i.i.d. data, a
square-integrable oracle score `ψ`, `L²`-consistent fitted scores and `√n`-negligible bias for
each fold), `√n (θ̂ₙ - θ)` converges in distribution to `N(0, Var_ν ψ)`, with `θ = ∫ ψ dν`.
The bias of a Neyman-orthogonal score is second order (for AIPW, `abs_aipwRemainder_le` bounds
it by a product of nuisance errors), so the bias condition holds under product rates such as
`‖ê - e*‖₂ ‖ĝ - g*‖₂ = o_P(n^{-1/2})`; no Donsker or entropy condition is assumed. -/
theorem tendstoInDistribution_crossFitEstimator {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {W : ℕ → Ω → 𝒲} (hW : ∀ i, Measurable (W i))
    (hindep : iIndepFun W P) (hident : ∀ i, IdentDistrib (W i) (W 0) P P)
    (hν : P.map (W 0) = ν) {ψ : 𝒲 → ℝ} (hψ : Measurable ψ) (hψ2 : MemLp ψ 2 ν) {K : ℕ}
    (fold : ℕ → ℕ → Fin K) {G : (n : ℕ) → (k : Fin K) → (trainFold fold n k → 𝒲) × 𝒲 → ℝ}
    (hG : ∀ n k, StronglyMeasurable (G n k)) (hG2 : ∀ n k u, MemLp (fun w => G n k (u, w)) 2 ν)
    (hcons : ∀ k, TendstoInMeasure P
      (fun n ω => ∫ w, (G n k (trainData W fold n k ω, w) - ψ w) ^ 2 ∂ν) atTop 0)
    (hbias : ∀ k, TendstoInMeasure P
      (fun (n : ℕ) ω => √(n : ℝ) * (∫ w, G n k (trainData W fold n k ω, w) ∂ν - ∫ w, ψ w ∂ν))
      atTop 0)
    {Z : Ω' → ℝ} (hZ : HasLaw Z (gaussianReal 0 Var[ψ; ν].toNNReal) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) * (crossFitEstimator W fold G n ω - ∫ w, ψ w ∂ν))
      atTop Z (fun _ => P) P' :=
  tendstoInDistribution_of_tendstoInMeasure_oracle_gap hW hindep hident hν hψ hψ2
    (fun n => (measurable_crossFitEstimator hW fold hG n).aemeasurable)
    (tendstoInMeasure_crossFitEstimator_sub_oracle hW hindep hident hν hψ hψ2 fold hG hG2 hcons
      hbias) hZ

end Asymptotic

section AIPWAsymptotic

open ProbabilityTheory Filter Topology

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} {m : MeasurableSpace 𝒲} [m𝒲 : MeasurableSpace 𝒲]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure 𝒲} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure P] in
/-- A constant multiple of a sequence tending to `0` in probability tends to `0`. -/
private lemma tendstoInMeasure_const_mul_zero (c : ℝ) {f : ℕ → Ω → ℝ}
    (hf : TendstoInMeasure P f atTop 0) : TendstoInMeasure P (fun n ω => c * f n ω) atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hf ⊢
  intro δ hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hf (δ / (|c| + 1)) (by positivity)) (fun _ => zero_le) fun n => measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs, abs_mul] at hω ⊢
  rw [div_le_iff₀ (by positivity)]
  nlinarith [abs_nonneg (f n ω), abs_nonneg c]

omit m in
/-- Joint measurability of the AIPW score with nuisances depending on a parameter. -/
private lemma measurable_aipwScoreOfSigma_uncurry {α : Type*} [MeasurableSpace α] {T : Set 𝒲}
    (hT : MeasurableSet T) {Y : 𝒲 → ℝ} (hY : Measurable Y) {e g₀ g₁ : α → 𝒲 → ℝ}
    (he : Measurable fun z : α × 𝒲 => e z.1 z.2) (hg₀ : Measurable fun z : α × 𝒲 => g₀ z.1 z.2)
    (hg₁ : Measurable fun z : α × 𝒲 => g₁ z.1 z.2) :
    Measurable fun z : α × 𝒲 => aipwScoreOfSigma T Y (e z.1) (g₀ z.1) (g₁ z.1) z.2 := by
  have hT' : MeasurableSet {z : α × 𝒲 | z.2 ∈ T} := measurable_snd hT
  have hYs : Measurable fun z : α × 𝒲 => Y z.2 := hY.comp measurable_snd
  have h : (fun z : α × 𝒲 => aipwScoreOfSigma T Y (e z.1) (g₀ z.1) (g₁ z.1) z.2) = fun z =>
      g₁ z.1 z.2 - g₀ z.1 z.2 +
        {z : α × 𝒲 | z.2 ∈ T}.indicator (fun z => (Y z.2 - g₁ z.1 z.2) / e z.1 z.2) z -
        {z : α × 𝒲 | z.2 ∈ T}ᶜ.indicator
          (fun z => (Y z.2 - g₀ z.1 z.2) / (1 - e z.1 z.2)) z := by
    funext z
    rw [aipwScoreOfSigma_apply]
    by_cases hz : z.2 ∈ T <;> simp [hz]
  rw [h]
  exact ((hg₁.sub hg₀).add (((hYs.sub hg₁).div he).indicator hT')).sub
    (((hYs.sub hg₀).div (measurable_const.sub he)).indicator hT'.compl)

omit m [IsProbabilityMeasure ν] in
/-- The AIPW score is square integrable when the outcome and the candidate regressions are
and the candidate propensity is bounded away from `0` and `1`. -/
private lemma memLp_aipwScoreOfSigma {T : Set 𝒲} (hT : MeasurableSet T) {Y e g₀ g₁ : 𝒲 → ℝ}
    (hY : MemLp Y 2 ν) (he : AEStronglyMeasurable e ν) (hg₀ : MemLp g₀ 2 ν)
    (hg₁ : MemLp g₁ 2 ν) {ε : ℝ} (hε : 0 < ε) (heε : ∀ᵐ w ∂ν, ε ≤ e w ∧ e w ≤ 1 - ε) :
    MemLp (aipwScoreOfSigma T Y e g₀ g₁) 2 ν := by
  have h : aipwScoreOfSigma T Y e g₀ g₁ = fun w => g₁ w - g₀ w +
      T.indicator (fun w => (Y w - g₁ w) / e w) w -
        Tᶜ.indicator (fun w => (Y w - g₀ w) / (1 - e w)) w := by
    funext w; exact aipwScoreOfSigma_apply T Y e g₀ g₁ w
  have harm : ∀ {S : Set 𝒲}, MeasurableSet S → ∀ {g p : 𝒲 → ℝ}, MemLp g 2 ν →
      AEStronglyMeasurable p ν → (∀ᵐ w ∂ν, ε ≤ p w) →
      MemLp (fun w => S.indicator (fun w => (Y w - g w) / p w) w) 2 ν := by
    intro S hS g p hg hp hpε
    refine MemLp.of_le_mul (c := ε⁻¹) (hY.sub hg) ?_ ?_
    · exact (((hY.aestronglyMeasurable.sub hg.aestronglyMeasurable).aemeasurable.div
        hp.aemeasurable).indicator hS).aestronglyMeasurable
    · filter_upwards [hpε] with w hw
      have hp0 : 0 < p w := hε.trans_le hw
      by_cases hwS : w ∈ S
      · simp only [Set.indicator_of_mem hwS, Real.norm_eq_abs, Pi.sub_apply, abs_div,
          abs_of_pos hp0]
        rw [div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_right (inv_anti₀ hε hw) (abs_nonneg _)
      · simp only [Set.indicator_of_notMem hwS, norm_zero]
        positivity
  rw [h]
  exact ((hg₁.sub hg₀).add (harm hT hg₁ he (heε.mono fun _ h => h.1))).sub
    (harm hT.compl hg₀ (aestronglyMeasurable_const.sub he) (heε.mono fun _ h => by linarith [h.2]))

/-- The oracle AIPW score: measurable, square integrable, with mean the average treatment
effect. -/
private lemma aipw_oracle_facts (hm : m ≤ m𝒲) {T : Set 𝒲} (hT : MeasurableSet T)
    {Y Y₀ Y₁ : 𝒲 → ℝ} (hY : Measurable Y) (hcons : Y =ᵐ[ν] observed T Y₀ Y₁)
    (hY₀ : MemLp Y₀ 2 ν) (hY₁ : MemLp Y₁ 2 ν)
    (hex₁ : ν[T.indicator Y₁ | m] =ᵐ[ν] ν[T.indicator 1 | m] * ν[Y₁ | m])
    (hex₀ : ν[Tᶜ.indicator Y₀ | m] =ᵐ[ν] (1 - ν[T.indicator 1 | m]) * ν[Y₀ | m])
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hpos : ∀ᵐ w ∂ν, ε₀ ≤ ν[T.indicator 1 | m] w ∧ ν[T.indicator 1 | m] w ≤ 1 - ε₀) :
    MemLp Y 2 ν ∧ Measurable (aipwScoreOfSigma T Y ν[T.indicator 1 | m] ν[Y₀ | m] ν[Y₁ | m]) ∧
      MemLp (aipwScoreOfSigma T Y ν[T.indicator 1 | m] ν[Y₀ | m] ν[Y₁ | m]) 2 ν ∧
      ∫ w, aipwScoreOfSigma T Y ν[T.indicator 1 | m] ν[Y₀ | m] ν[Y₁ | m] w ∂ν =
        ∫ w, (Y₁ w - Y₀ w) ∂ν := by
  set eS := ν[T.indicator (1 : 𝒲 → ℝ) | m] with heS
  have heSm : StronglyMeasurable[m] eS := stronglyMeasurable_condExp
  have hμ₀Sm : StronglyMeasurable[m] ν[Y₀ | m] := stronglyMeasurable_condExp
  have hμ₁Sm : StronglyMeasurable[m] ν[Y₁ | m] := stronglyMeasurable_condExp
  have hY2 : MemLp Y 2 ν := by
    refine MemLp.ae_eq hcons.symm ?_
    exact (hY₁.indicator hT.nullMeasurableSet).add (hY₀.indicator hT.compl.nullMeasurableSet)
  refine ⟨hY2, ?_, ?_, ?_⟩
  · exact (measurable_aipwScoreOfSigma_uncurry (α := Unit) hT hY (e := fun _ => eS)
      (g₀ := fun _ => ν[Y₀ | m]) (g₁ := fun _ => ν[Y₁ | m])
      ((heSm.mono hm).measurable.comp measurable_snd)
      ((hμ₀Sm.mono hm).measurable.comp measurable_snd)
      ((hμ₁Sm.mono hm).measurable.comp measurable_snd)).comp
      ((measurable_const (a := ())).prodMk measurable_id)
  · exact memLp_aipwScoreOfSigma hT hY2 (heSm.mono hm).aestronglyMeasurable
      (MemLp.condExp (m := m) one_le_two hY₀) (MemLp.condExp (m := m) one_le_two hY₁) hε₀ hpos
  · exact integral_aipwScoreOfSigma_of_propensity hm hT hcons (hY₀.integrable one_le_two)
      (hY₁.integrable one_le_two) hex₁ hex₀ heSm hμ₀Sm hμ₁Sm integrable_condExp
      integrable_condExp hε₀ hpos (ae_eq_refl _)

/-- **The cross-fitted AIPW estimator is `√n`-equivalent to the oracle AIPW estimator.**
`W 0, W 1, …` are i.i.d. full-data observations with law `ν`; `T` is the treatment event,
`Y = observed T Y₀ Y₁` the observed outcome, `m` the covariate σ-algebra, `e* = P(T | m)`,
`μₐ* = E[Yₐ | m]`. Assume mean exchangeability, strong overlap `ε₀ ≤ e* ≤ 1 - ε₀`, square
integrable potential outcomes, and fitted nuisances `ê, ĝ₀, ĝ₁` for each fold that depend only on
that fold's training data, are `m`-measurable, square integrable, and clipped to `[ε, 1 - ε]`.
If, for each fold,
* the fitted AIPW score is `L²`-consistent for the oracle score `ψ* = ψ(e*, μ₀*, μ₁*)`, and
* the product of nuisance errors is `o_P(n^{-1/2})`:
  `√n ‖e* - ê‖₂ (‖μ₁* - ĝ₁‖₂ + ‖μ₀* - ĝ₀‖₂) → 0` in probability,
then `√n (τ̂ₙ - τ̂ₙ*) → 0` in probability, where `τ̂ₙ` is the cross-fitted AIPW estimator and
`τ̂ₙ* = n⁻¹ ∑_{i < n} ψ*(W i)` the oracle AIPW estimator with the true nuisances.

Correspondence with T143: this is the remainder hypothesis `hrem` (`√n (τ̂ - τ̂*) → 0` in
probability, with `τ̂*` the oracle AIPW estimator at the true nuisances) of the T143 AIPW
asymptotic-normality development, for the cross-fitted `τ̂`. After both are merged, `hrem` is
obtained from this theorem by identifying T143's oracle score with
`aipwScoreOfSigma T Y e* μ₀* μ₁*` (both are `MissingOutcomes.aipwATEScore`-based). -/
theorem tendstoInMeasure_crossFit_aipw_sub_oracle {W : ℕ → Ω → 𝒲} (hW : ∀ i, Measurable (W i))
    (hindep : iIndepFun W P) (hident : ∀ i, IdentDistrib (W i) (W 0) P P)
    (hν : P.map (W 0) = ν) (hm : m ≤ m𝒲) {T : Set 𝒲} (hT : MeasurableSet T)
    {Y Y₀ Y₁ : 𝒲 → ℝ} (hY : Measurable Y) (hcons : Y =ᵐ[ν] observed T Y₀ Y₁)
    (hY₀ : MemLp Y₀ 2 ν) (hY₁ : MemLp Y₁ 2 ν)
    (hex₁ : ν[T.indicator Y₁ | m] =ᵐ[ν] ν[T.indicator 1 | m] * ν[Y₁ | m])
    (hex₀ : ν[Tᶜ.indicator Y₀ | m] =ᵐ[ν] (1 - ν[T.indicator 1 | m]) * ν[Y₀ | m])
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hpos : ∀ᵐ w ∂ν, ε₀ ≤ ν[T.indicator 1 | m] w ∧ ν[T.indicator 1 | m] w ≤ 1 - ε₀)
    {K : ℕ} (fold : ℕ → ℕ → Fin K)
    {ê ĝ₀ ĝ₁ : (n : ℕ) → (k : Fin K) → (trainFold fold n k → 𝒲) → 𝒲 → ℝ}
    (hêm : ∀ n k, Measurable fun z : (trainFold fold n k → 𝒲) × 𝒲 => ê n k z.1 z.2)
    (hĝ₀m : ∀ n k, Measurable fun z : (trainFold fold n k → 𝒲) × 𝒲 => ĝ₀ n k z.1 z.2)
    (hĝ₁m : ∀ n k, Measurable fun z : (trainFold fold n k → 𝒲) × 𝒲 => ĝ₁ n k z.1 z.2)
    (hêσ : ∀ n k u, StronglyMeasurable[m] (ê n k u))
    (hĝ₀σ : ∀ n k u, StronglyMeasurable[m] (ĝ₀ n k u))
    (hĝ₁σ : ∀ n k u, StronglyMeasurable[m] (ĝ₁ n k u))
    (hĝ₀2 : ∀ n k u, MemLp (ĝ₀ n k u) 2 ν) (hĝ₁2 : ∀ n k u, MemLp (ĝ₁ n k u) 2 ν)
    {ε : ℝ} (hε : 0 < ε) (hêε : ∀ n k u w, ε ≤ ê n k u w ∧ ê n k u w ≤ 1 - ε)
    (hL2 : ∀ k, TendstoInMeasure P (fun n ω => ∫ w,
      (aipwScoreOfSigma T Y (ê n k (trainData W fold n k ω)) (ĝ₀ n k (trainData W fold n k ω))
          (ĝ₁ n k (trainData W fold n k ω)) w -
        aipwScoreOfSigma T Y ν[T.indicator 1 | m] ν[Y₀ | m] ν[Y₁ | m] w) ^ 2 ∂ν) atTop 0)
    (hrate : ∀ k, TendstoInMeasure P (fun (n : ℕ) ω => √(n : ℝ) *
      (√(∫ w, (ν[T.indicator 1 | m] w - ê n k (trainData W fold n k ω) w) ^ 2 ∂ν) *
        (√(∫ w, (ν[Y₁ | m] w - ĝ₁ n k (trainData W fold n k ω) w) ^ 2 ∂ν) +
          √(∫ w, (ν[Y₀ | m] w - ĝ₀ n k (trainData W fold n k ω) w) ^ 2 ∂ν)))) atTop 0) :
    TendstoInMeasure P (fun (n : ℕ) ω => √(n : ℝ) *
      (crossFitEstimator W fold (fun n k z =>
        aipwScoreOfSigma T Y (ê n k z.1) (ĝ₀ n k z.1) (ĝ₁ n k z.1) z.2) n ω -
          (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
            aipwScoreOfSigma T Y ν[T.indicator 1 | m] ν[Y₀ | m] ν[Y₁ | m] (W i ω))) atTop 0 := by
  obtain ⟨hY2, hψm, hψ2, hθ⟩ :=
    aipw_oracle_facts hm hT hY hcons hY₀ hY₁ hex₁ hex₀ hε₀ hpos
  set eS := ν[T.indicator (1 : 𝒲 → ℝ) | m] with heS
  set μ₀S := ν[Y₀ | m] with hμ₀S
  set μ₁S := ν[Y₁ | m] with hμ₁S
  have hY₀i : Integrable Y₀ ν := hY₀.integrable one_le_two
  have hY₁i : Integrable Y₁ ν := hY₁.integrable one_le_two
  refine tendstoInMeasure_crossFitEstimator_sub_oracle hW hindep hident hν hψm hψ2 fold
    (fun n k => (measurable_aipwScoreOfSigma_uncurry hT hY (hêm n k) (hĝ₀m n k)
      (hĝ₁m n k)).stronglyMeasurable)
    (fun n k u => memLp_aipwScoreOfSigma hT hY2 ((hêσ n k u).mono hm).aestronglyMeasurable
      (hĝ₀2 n k u) (hĝ₁2 n k u) hε (ae_of_all _ (hêε n k u))) hL2 ?_
  intro k
  refine tendstoInMeasure_zero_of_abs_le (tendstoInMeasure_const_mul_zero ε⁻¹ (hrate k))
    fun n ω => ?_
  set u := trainData W fold n k ω
  have hrem : ∫ w, aipwScoreOfSigma T Y (ê n k u) (ĝ₀ n k u) (ĝ₁ n k u) w ∂ν -
      ∫ w, aipwScoreOfSigma T Y eS μ₀S μ₁S w ∂ν =
        aipwRemainder ν m T Y₀ Y₁ (ê n k u) (ĝ₀ n k u) (ĝ₁ n k u) := by
    rw [hθ]
    exact integral_aipwScoreOfSigma_sub hm hT hcons hY₀i hY₁i hex₁ hex₀ (hêσ n k u)
      (hĝ₀σ n k u) (hĝ₁σ n k u) ((hĝ₀2 n k u).integrable one_le_two)
      ((hĝ₁2 n k u).integrable one_le_two) hε (ae_of_all _ (hêε n k u))
  have hb := abs_aipwRemainder_le (m := m) hT hY₀ hY₁ ((hêσ n k u).mono hm).aestronglyMeasurable
    (hĝ₀2 n k u) (hĝ₁2 n k u) hε (ae_of_all _ (hêε n k u))
  rw [hrem, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc √(n : ℝ) * |aipwRemainder ν m T Y₀ Y₁ (ê n k u) (ĝ₀ n k u) (ĝ₁ n k u)|
      ≤ √(n : ℝ) * (ε⁻¹ * √(∫ w, (eS w - ê n k u w) ^ 2 ∂ν) *
          (√(∫ w, (μ₁S w - ĝ₁ n k u w) ^ 2 ∂ν) + √(∫ w, (μ₀S w - ĝ₀ n k u w) ^ 2 ∂ν))) :=
        mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
    _ = |ε⁻¹ * (√(n : ℝ) * (√(∫ w, (eS w - ê n k u w) ^ 2 ∂ν) *
          (√(∫ w, (μ₁S w - ĝ₁ n k u w) ^ 2 ∂ν) + √(∫ w, (μ₀S w - ĝ₀ n k u w) ^ 2 ∂ν))))| := by
        rw [abs_of_nonneg (by positivity)]
        ring

/-- **Asymptotic normality of the cross-fitted AIPW estimator.** Under the hypotheses of
`tendstoInMeasure_crossFit_aipw_sub_oracle` (i.i.d. data, consistency, mean exchangeability,
strong overlap, clipped fitted propensities, `L²`-consistent fitted scores and nuisance-error
products of order `o_P(n^{-1/2})`), `√n (τ̂ₙ - E[Y₁ - Y₀])` converges in distribution to
`N(0, Var ψ*)`, where `ψ* = ψ(e*, μ₀*, μ₁*)` is the oracle AIPW score (its variance is the
semiparametric efficiency bound for the ATE; that optimality is not formalized here). Each
nuisance may converge slower than `n^{-1/2}` (e.g. both at `o_P(n^{-1/4})`), and no Donsker
condition on the nuisance estimators is assumed. -/
theorem tendstoInDistribution_crossFit_aipw {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {W : ℕ → Ω → 𝒲} (hW : ∀ i, Measurable (W i))
    (hindep : iIndepFun W P) (hident : ∀ i, IdentDistrib (W i) (W 0) P P)
    (hν : P.map (W 0) = ν) (hm : m ≤ m𝒲) {T : Set 𝒲} (hT : MeasurableSet T)
    {Y Y₀ Y₁ : 𝒲 → ℝ} (hY : Measurable Y) (hcons : Y =ᵐ[ν] observed T Y₀ Y₁)
    (hY₀ : MemLp Y₀ 2 ν) (hY₁ : MemLp Y₁ 2 ν)
    (hex₁ : ν[T.indicator Y₁ | m] =ᵐ[ν] ν[T.indicator 1 | m] * ν[Y₁ | m])
    (hex₀ : ν[Tᶜ.indicator Y₀ | m] =ᵐ[ν] (1 - ν[T.indicator 1 | m]) * ν[Y₀ | m])
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hpos : ∀ᵐ w ∂ν, ε₀ ≤ ν[T.indicator 1 | m] w ∧ ν[T.indicator 1 | m] w ≤ 1 - ε₀)
    {K : ℕ} (fold : ℕ → ℕ → Fin K)
    {ê ĝ₀ ĝ₁ : (n : ℕ) → (k : Fin K) → (trainFold fold n k → 𝒲) → 𝒲 → ℝ}
    (hêm : ∀ n k, Measurable fun z : (trainFold fold n k → 𝒲) × 𝒲 => ê n k z.1 z.2)
    (hĝ₀m : ∀ n k, Measurable fun z : (trainFold fold n k → 𝒲) × 𝒲 => ĝ₀ n k z.1 z.2)
    (hĝ₁m : ∀ n k, Measurable fun z : (trainFold fold n k → 𝒲) × 𝒲 => ĝ₁ n k z.1 z.2)
    (hêσ : ∀ n k u, StronglyMeasurable[m] (ê n k u))
    (hĝ₀σ : ∀ n k u, StronglyMeasurable[m] (ĝ₀ n k u))
    (hĝ₁σ : ∀ n k u, StronglyMeasurable[m] (ĝ₁ n k u))
    (hĝ₀2 : ∀ n k u, MemLp (ĝ₀ n k u) 2 ν) (hĝ₁2 : ∀ n k u, MemLp (ĝ₁ n k u) 2 ν)
    {ε : ℝ} (hε : 0 < ε) (hêε : ∀ n k u w, ε ≤ ê n k u w ∧ ê n k u w ≤ 1 - ε)
    (hL2 : ∀ k, TendstoInMeasure P (fun n ω => ∫ w,
      (aipwScoreOfSigma T Y (ê n k (trainData W fold n k ω)) (ĝ₀ n k (trainData W fold n k ω))
          (ĝ₁ n k (trainData W fold n k ω)) w -
        aipwScoreOfSigma T Y ν[T.indicator 1 | m] ν[Y₀ | m] ν[Y₁ | m] w) ^ 2 ∂ν) atTop 0)
    (hrate : ∀ k, TendstoInMeasure P (fun (n : ℕ) ω => √(n : ℝ) *
      (√(∫ w, (ν[T.indicator 1 | m] w - ê n k (trainData W fold n k ω) w) ^ 2 ∂ν) *
        (√(∫ w, (ν[Y₁ | m] w - ĝ₁ n k (trainData W fold n k ω) w) ^ 2 ∂ν) +
          √(∫ w, (ν[Y₀ | m] w - ĝ₀ n k (trainData W fold n k ω) w) ^ 2 ∂ν)))) atTop 0)
    {Z : Ω' → ℝ} (hZ : HasLaw Z
      (gaussianReal 0
        Var[aipwScoreOfSigma T Y ν[T.indicator 1 | m] ν[Y₀ | m] ν[Y₁ | m]; ν].toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (crossFitEstimator W fold (fun n k z =>
        aipwScoreOfSigma T Y (ê n k z.1) (ĝ₀ n k z.1) (ĝ₁ n k z.1) z.2) n ω -
          ∫ w, (Y₁ w - Y₀ w) ∂ν)) atTop Z (fun _ => P) P' := by
  obtain ⟨-, hψm, hψ2, hθ⟩ := aipw_oracle_facts hm hT hY hcons hY₀ hY₁ hex₁ hex₀ hε₀ hpos
  rw [← hθ]
  exact tendstoInDistribution_of_tendstoInMeasure_oracle_gap hW hindep hident hν hψm hψ2
    (fun n => (measurable_crossFitEstimator hW fold (fun n k =>
      (measurable_aipwScoreOfSigma_uncurry hT hY (hêm n k) (hĝ₀m n k)
        (hĝ₁m n k)).stronglyMeasurable) n).aemeasurable)
    (tendstoInMeasure_crossFit_aipw_sub_oracle hW hindep hident hν hm hT hY hcons hY₀ hY₁
      hex₁ hex₀ hε₀ hpos fold hêm hĝ₀m hĝ₁m hêσ hĝ₀σ hĝ₁σ hĝ₀2 hĝ₁2 hε hêε hL2 hrate) hZ

end AIPWAsymptotic

end MathlibExt.Probability.Causality.AugmentedIPW.CrossFitting
