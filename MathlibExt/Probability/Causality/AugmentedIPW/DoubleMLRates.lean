/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.AugmentedIPW.CrossFitting

/-!
# Double machine learning: rate conditions for cross-fitted AIPW

`CrossFitting.tendstoInDistribution_crossFit_aipw` proves asymptotic normality of the
cross-fitted AIPW estimator of the average treatment effect assuming, for each fold, that
* the fitted AIPW score is `L²`-consistent for the oracle score (`hL2`), and
* the product of nuisance errors is `o_P(n^{-1/2})` (`hrate`).

The first hypothesis is a statement about the score, not about the nuisance estimators. This file
replaces it with rate conditions on the nuisances themselves, modeled on Chernozhukov et al.
(2018, Assumption 5.1): `L²` consistency of the fitted propensity and outcome regressions,
together with a bounded conditional variance of each potential outcome. The variance bound is
stronger than the paper's noise condition (see "Hypotheses and scope"). The product-rate
condition then gives asymptotic normality with no condition on the fitted score.

## Main results

* `abs_aipwScoreOfSigma_sub_le`: a pointwise bound on the difference between the AIPW score at
  candidate nuisances `(e, g₀, g₁)` and at the true ones `(e*, μ₀*, μ₁*)`, by the nuisance errors
  and the outcome noise `Yₐ - μₐ*`.
* `integral_sq_aipwScoreOfSigma_sub_le`: the `L²` score error is bounded by the `L²` nuisance
  errors. If `ε ≤ e ≤ 1 - ε`, `ε₀ ≤ e* ≤ 1 - ε₀` and `Var(Yₐ | m) ≤ C`, then
  `‖ψ(e, g) - ψ*‖₂² ≤ 4 (1 + ε⁻¹)² (‖μ₁* - g₁‖₂² + ‖μ₀* - g₀‖₂²) + 8 C (ε ε₀)⁻² ‖e* - e‖₂²`.
* `tendstoInMeasure_integral_sq_crossFit_aipw_sub`: nuisance `L²` consistency in probability
  implies the score `L²` consistency hypothesis `hL2` of the cross-fitting theorems.
* `tendstoInDistribution_crossFit_aipw_of_rates`: **double/debiased ML under rate conditions.**
  Nuisance consistency, bounded conditional outcome variance and the product rate
  `√n ‖e* - ê‖₂ (‖μ₁* - ĝ₁‖₂ + ‖μ₀* - ĝ₀‖₂) → 0` in probability give
  `√n (τ̂ₙ - τ) → N(0, Var ψ*)`.
* `tendstoInDistribution_crossFit_aipw_of_quarter_rates`: the special case where every nuisance
  converges at rate `o_P(n^{-1/4})` in `L²`, stated as `√n ‖e* - ê‖₂² → 0` (likewise for
  `ĝ₀, ĝ₁`) in probability. Neither consistency nor the product rate is assumed separately.

## Hypotheses and scope

* The outcome-noise condition is `E[(Yₐ - E[Yₐ | m])² | m] ≤ C` a.e. for both arms: a bound on
  the conditional variance of each potential outcome. It is stronger than the noise condition of
  Chernozhukov et al. (2018, Assumption 5.1; arXiv:1608.00060v6, eqs. (5.1)–(5.2)), which bounds
  `‖E[U² | X]‖_∞` for the residual `U = Y - g₀(D, X)`, `E[U | X, D] = 0`, of the observed outcome
  after regressing on treatment and covariates. Under consistency and mean exchangeability,
  `E[Y | T, m] = 1_T μ₁* + 1_{Tᶜ} μ₀*`, so `U² = 1_T (Y₁ - μ₁*)² + 1_{Tᶜ} (Y₀ - μ₀*)²` and the
  condition here gives `E[U² | m] ≤ 2C`. The converse needs more than mean exchangeability: the
  paper's bound `C'` controls only `E[1_T (Y₁ - μ₁*)² | m]` and `E[1_{Tᶜ} (Y₀ - μ₀*)² | m]`,
  which give `E[(Yₐ - μₐ*)² | m] ≤ C' / ε₀` when, for example, `(Yₐ - μₐ*)²` is conditionally
  mean independent of the treatment given the covariates. The condition here is used only to
  bound the cross term
  `E[(Yₐ - μₐ*)² (e* - ê)²] ≤ C ‖e* - ê‖₂²`, through the pull-out property of the conditional
  expectation; the fitted propensity must therefore be `m`-measurable, as in `CrossFitting`.
* The remaining hypotheses (i.i.d. data, consistency, mean exchangeability, strong overlap,
  clipped fitted propensities, measurability and square integrability of the fitted nuisances)
  are those of `CrossFitting.tendstoInDistribution_crossFit_aipw`.
* Rates are stated as convergence in probability over the training sample, so the nuisance
  errors may be random; deterministic rates (`‖·‖₂ ≤ δₙ` surely) are a special case.

## References

* V. Chernozhukov, D. Chetverikov, M. Demirer, E. Duflo, C. Hansen, W. Newey and J. Robins,
  *Double/debiased machine learning for treatment and structural parameters*, Econometrics
  Journal 21(1) (2018), C1–C68, Section 5.1 (Assumption 5.1 and Theorem 5.1): the ATE
  application, its nuisance rate conditions and the product rate `‖m̂ - m‖₂ ‖ĝ - g‖₂ = o(n^{-1/2})`.
* E. H. Kennedy, *Semiparametric doubly robust targeted double machine learning: a review*,
  arXiv:2203.06469v2 (2023): the `o_P(n^{-1/4})` sufficient condition.
-/

@[expose] public section

namespace MathlibExt.Probability.Causality.AugmentedIPW.DoubleMLRates

open MeasureTheory ProbabilityTheory Filter Topology MathlibExt.Probability.Causality
open MathlibExt.Probability.Causality.AugmentedIPW.CrossFitting

section ScoreError

/-- One arm of the AIPW score: `|(y - g) / p - (y - μ) / q|` is at most
`ε⁻¹ |μ - g| + ε⁻¹ ε₀⁻¹ |y - μ| |q - p|` when `p ≥ ε > 0` and `q ≥ ε₀ > 0`. -/
private lemma abs_arm_sub_le {y g μ p q ε ε₀ : ℝ} (hε : 0 < ε) (hε₀ : 0 < ε₀) (hp : ε ≤ p)
    (hq : ε₀ ≤ q) :
    |(y - g) / p - (y - μ) / q| ≤ ε⁻¹ * |μ - g| + ε⁻¹ * ε₀⁻¹ * (|y - μ| * |q - p|) := by
  have hp0 : 0 < p := hε.trans_le hp
  have hq0 : 0 < q := hε₀.trans_le hq
  have h : (y - g) / p - (y - μ) / q = (μ - g) / p + (y - μ) * (q - p) / (p * q) := by
    field_simp; ring
  rw [h]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos hp0, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hε hp) (abs_nonneg _)
  · rw [abs_div, abs_mul, abs_of_pos (mul_pos hp0 hq0), div_eq_inv_mul, mul_inv]
    gcongr

/-- `|x| ≤ a + b + c + d` implies `x² ≤ 4 (a² + b² + c² + d²)`. -/
private lemma sq_le_four_mul {x a b c d : ℝ} (h : |x| ≤ a + b + c + d) :
    x ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  have hx : x ^ 2 ≤ (a + b + c + d) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg x) h 2
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

variable {𝒲 : Type*} {m m𝒲 : MeasurableSpace 𝒲} {ν : Measure 𝒲}

/-- **Pointwise AIPW score error.** At a point where the observed outcome is `Y₁` or `Y₀`
according to the treatment, the candidate propensity lies in `[ε, 1 - ε]` and the reference
propensity `e*` in `[ε₀, 1 - ε₀]`, the score at candidate nuisances `(e, g₀, g₁)` differs from
the score at reference nuisances `(e*, μ₀, μ₁)` by at most
`(1 + ε⁻¹) (|μ₁ - g₁| + |μ₀ - g₀|) + ε⁻¹ ε₀⁻¹ (|Y₁ - μ₁| + |Y₀ - μ₀|) |e* - e|`. -/
theorem abs_aipwScoreOfSigma_sub_le {T : Set 𝒲} {Y Y₀ Y₁ e g₀ g₁ es μ₀ μ₁ : 𝒲 → ℝ} {w : 𝒲}
    {ε ε₀ : ℝ} (hε : 0 < ε) (hε₀ : 0 < ε₀) (hY : Y w = observed T Y₀ Y₁ w)
    (he : ε ≤ e w ∧ e w ≤ 1 - ε) (hes : ε₀ ≤ es w ∧ es w ≤ 1 - ε₀) :
    |aipwScoreOfSigma T Y e g₀ g₁ w - aipwScoreOfSigma T Y es μ₀ μ₁ w| ≤
      (1 + ε⁻¹) * |μ₁ w - g₁ w| + (1 + ε⁻¹) * |μ₀ w - g₀ w| +
        ε⁻¹ * ε₀⁻¹ * (|Y₁ w - μ₁ w| * |es w - e w|) +
          ε⁻¹ * ε₀⁻¹ * (|Y₀ w - μ₀ w| * |es w - e w|) := by
  have hκ : 0 ≤ ε⁻¹ * ε₀⁻¹ := by positivity
  have hεi : 0 ≤ ε⁻¹ := by positivity
  have h₁ := abs_nonneg (μ₁ w - g₁ w)
  have h₀ := abs_nonneg (μ₀ w - g₀ w)
  have hU₁ : 0 ≤ |Y₁ w - μ₁ w| * |es w - e w| := by positivity
  have hU₀ : 0 ≤ |Y₀ w - μ₀ w| * |es w - e w| := by positivity
  have hsum := abs_add_le (-(μ₁ w - g₁ w)) (μ₀ w - g₀ w)
  rw [abs_neg] at hsum
  by_cases hw : w ∈ T
  · have hYw : Y w = Y₁ w := by simp [hY, observed, hw]
    have harm := abs_arm_sub_le (y := Y₁ w) (g := g₁ w) (μ := μ₁ w) hε hε₀ he.1 hes.1
    have hd : aipwScoreOfSigma T Y e g₀ g₁ w - aipwScoreOfSigma T Y es μ₀ μ₁ w =
        -(μ₁ w - g₁ w) + (μ₀ w - g₀ w) + ((Y₁ w - g₁ w) / e w - (Y₁ w - μ₁ w) / es w) := by
      simp only [aipwScoreOfSigma_apply, Set.indicator_of_mem hw,
        Set.indicator_of_notMem (Set.notMem_compl_iff.2 hw), hYw]
      ring
    rw [hd]
    have h2 := abs_add_le (-(μ₁ w - g₁ w) + (μ₀ w - g₀ w))
      ((Y₁ w - g₁ w) / e w - (Y₁ w - μ₁ w) / es w)
    nlinarith [mul_nonneg hεi h₀, mul_nonneg hκ hU₀]
  · have hYw : Y w = Y₀ w := by simp [hY, observed, hw]
    have harm := abs_arm_sub_le (y := Y₀ w) (g := g₀ w) (μ := μ₀ w) (p := 1 - e w)
      (q := 1 - es w) hε hε₀ (by linarith [he.2]) (by linarith [hes.2])
    have hqp : |1 - es w - (1 - e w)| = |es w - e w| := by
      rw [show 1 - es w - (1 - e w) = -(es w - e w) by ring, abs_neg]
    rw [hqp] at harm
    have hd : aipwScoreOfSigma T Y e g₀ g₁ w - aipwScoreOfSigma T Y es μ₀ μ₁ w =
        -(μ₁ w - g₁ w) + (μ₀ w - g₀ w) -
          ((Y₀ w - g₀ w) / (1 - e w) - (Y₀ w - μ₀ w) / (1 - es w)) := by
      simp only [aipwScoreOfSigma_apply, Set.indicator_of_notMem hw,
        Set.indicator_of_mem (Set.mem_compl hw), hYw]
      ring
    rw [hd]
    have h2 := abs_sub (-(μ₁ w - g₁ w) + (μ₀ w - g₀ w))
      ((Y₀ w - g₀ w) / (1 - e w) - (Y₀ w - μ₀ w) / (1 - es w))
    nlinarith [mul_nonneg hεi h₁, mul_nonneg hκ hU₁]

/-- `∫ f h ≤ C ∫ h` for a bounded nonnegative `m`-measurable weight `h` when `E[f | m] ≤ C`. -/
private lemma integral_mul_le_of_condExp_le [IsFiniteMeasure ν] (hm : m ≤ m𝒲) {f h : 𝒲 → ℝ}
    (hf : Integrable f ν) (hh : StronglyMeasurable[m] h) {B : ℝ} (hhB : ∀ᵐ w ∂ν, |h w| ≤ B)
    (hh0 : ∀ᵐ w ∂ν, 0 ≤ h w) {C : ℝ} (hfC : ν[f | m] ≤ᵐ[ν] fun _ => C) :
    ∫ w, f w * h w ∂ν ≤ C * ∫ w, h w ∂ν := by
  have hhm : StronglyMeasurable h := hh.mono hm
  have hhB' : ∀ᵐ w ∂ν, ‖h w‖ ≤ B := hhB.mono fun w hw => by rwa [Real.norm_eq_abs]
  have hfh : Integrable (f * h) ν := hf.mul_bdd hhm.aestronglyMeasurable hhB'
  have hhi : Integrable h ν := Integrable.of_bound hhm.aestronglyMeasurable B hhB'
  calc ∫ w, f w * h w ∂ν = ∫ w, (f * h) w ∂ν := rfl
    _ = ∫ w, ν[f * h | m] w ∂ν := (integral_condExp hm).symm
    _ = ∫ w, (ν[f | m] * h) w ∂ν :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_right hh hfh hf)
    _ ≤ ∫ w, C * h w ∂ν := by
        refine integral_mono_ae (integrable_condExp.mul_bdd hhm.aestronglyMeasurable hhB')
          (hhi.const_mul C) ?_
        filter_upwards [hfC, hh0] with w hw h0
        exact mul_le_mul_of_nonneg_right hw h0
    _ = C * ∫ w, h w ∂ν := integral_const_mul _ _

/-- **The `L²` error of the AIPW score is bounded by the `L²` nuisance errors.** Let `m` be the
covariate σ-algebra, `e* = P(T | m)`, `μₐ* = E[Yₐ | m]`, and assume consistency
`Y = observed T Y₀ Y₁` a.e., square integrable potential outcomes, strong overlap
`ε₀ ≤ e* ≤ 1 - ε₀`, and bounded conditional variances `E[(Yₐ - μₐ*)² | m] ≤ C`. For an
`m`-measurable candidate propensity `e` in `[ε, 1 - ε]` and square integrable candidate outcome
regressions `g₀, g₁`,
`‖ψ(e, g₀, g₁) - ψ(e*, μ₀*, μ₁*)‖₂² ≤
  4 (1 + ε⁻¹)² (‖μ₁* - g₁‖₂² + ‖μ₀* - g₀‖₂²) + 8 C (ε⁻¹ ε₀⁻¹)² ‖e* - e‖₂²`. -/
theorem integral_sq_aipwScoreOfSigma_sub_le [IsProbabilityMeasure ν] (hm : m ≤ m𝒲) {T : Set 𝒲}
    {Y Y₀ Y₁ : 𝒲 → ℝ} (hcons : Y =ᵐ[ν] observed T Y₀ Y₁) (hY₀ : MemLp Y₀ 2 ν)
    (hY₁ : MemLp Y₁ 2 ν) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hpos : ∀ᵐ w ∂ν, ε₀ ≤ ν[T.indicator 1 | m] w ∧ ν[T.indicator 1 | m] w ≤ 1 - ε₀) {C : ℝ}
    (hvar₀ : ν[fun w => (Y₀ w - ν[Y₀ | m] w) ^ 2 | m] ≤ᵐ[ν] fun _ => C)
    (hvar₁ : ν[fun w => (Y₁ w - ν[Y₁ | m] w) ^ 2 | m] ≤ᵐ[ν] fun _ => C)
    {e g₀ g₁ : 𝒲 → ℝ} (he : StronglyMeasurable[m] e) (hg₀ : MemLp g₀ 2 ν)
    (hg₁ : MemLp g₁ 2 ν) {ε : ℝ} (hε : 0 < ε) (heε : ∀ᵐ w ∂ν, ε ≤ e w ∧ e w ≤ 1 - ε) :
    ∫ w, (aipwScoreOfSigma T Y e g₀ g₁ w -
        aipwScoreOfSigma T Y ν[T.indicator 1 | m] ν[Y₀ | m] ν[Y₁ | m] w) ^ 2 ∂ν ≤
      4 * (1 + ε⁻¹) ^ 2 * (∫ w, (ν[Y₁ | m] w - g₁ w) ^ 2 ∂ν + ∫ w, (ν[Y₀ | m] w - g₀ w) ^ 2 ∂ν) +
        8 * C * (ε⁻¹ * ε₀⁻¹) ^ 2 * ∫ w, (ν[T.indicator 1 | m] w - e w) ^ 2 ∂ν := by
  set es := ν[T.indicator (1 : 𝒲 → ℝ) | m] with hes
  set μ₀ := ν[Y₀ | m] with hμ₀
  set μ₁ := ν[Y₁ | m] with hμ₁
  set c := 1 + ε⁻¹ with hc
  set κ := ε⁻¹ * ε₀⁻¹ with hκ
  have hb₁ : MemLp (fun w => μ₁ w - g₁ w) 2 ν := (MemLp.condExp (m := m) one_le_two hY₁).sub hg₁
  have hb₀ : MemLp (fun w => μ₀ w - g₀ w) 2 ν := (MemLp.condExp (m := m) one_le_two hY₀).sub hg₀
  have hU₁ : MemLp (fun w => Y₁ w - μ₁ w) 2 ν := hY₁.sub (MemLp.condExp (m := m) one_le_two hY₁)
  have hU₀ : MemLp (fun w => Y₀ w - μ₀ w) 2 ν := hY₀.sub (MemLp.condExp (m := m) one_le_two hY₀)
  have haσ : StronglyMeasurable[m] (fun w => (es w - e w) ^ 2) :=
    (stronglyMeasurable_condExp.sub he).pow 2
  have ha1 : ∀ᵐ w ∂ν, |(es w - e w) ^ 2| ≤ 1 := by
    filter_upwards [hpos, heε] with w h₁ h₂
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have ha0 : ∀ᵐ w ∂ν, 0 ≤ (es w - e w) ^ 2 := ae_of_all _ fun _ => sq_nonneg _
  have haS : AEStronglyMeasurable (fun w => (es w - e w) ^ 2) ν :=
    (haσ.mono hm).aestronglyMeasurable
  have hUa : ∀ {U : 𝒲 → ℝ}, MemLp U 2 ν → Integrable (fun w => U w ^ 2 * (es w - e w) ^ 2) ν :=
    fun hU => hU.integrable_sq.mul_bdd haS (ha1.mono fun w hw => by rwa [Real.norm_eq_abs])
  have hcU : ∀ {U : 𝒲 → ℝ}, MemLp U 2 ν → ν[fun w => U w ^ 2 | m] ≤ᵐ[ν] (fun _ => C) →
      ∫ w, U w ^ 2 * (es w - e w) ^ 2 ∂ν ≤ C * ∫ w, (es w - e w) ^ 2 ∂ν :=
    fun hU hC => integral_mul_le_of_condExp_le hm hU.integrable_sq haσ ha1 ha0 hC
  have hpt : ∀ᵐ w ∂ν, (aipwScoreOfSigma T Y e g₀ g₁ w - aipwScoreOfSigma T Y es μ₀ μ₁ w) ^ 2 ≤
      4 * c ^ 2 * (μ₁ w - g₁ w) ^ 2 + 4 * c ^ 2 * (μ₀ w - g₀ w) ^ 2 +
        4 * κ ^ 2 * ((Y₁ w - μ₁ w) ^ 2 * (es w - e w) ^ 2) +
          4 * κ ^ 2 * ((Y₀ w - μ₀ w) ^ 2 * (es w - e w) ^ 2) := by
    filter_upwards [hcons, hpos, heε] with w hYw h₁ h₂
    have h := sq_le_four_mul (abs_aipwScoreOfSigma_sub_le (g₀ := g₀) (g₁ := g₁) (μ₀ := μ₀)
      (μ₁ := μ₁) hε hε₀ hYw h₂ h₁)
    refine h.trans_eq ?_
    simp only [mul_pow, sq_abs]
    ring
  have hi₁ : Integrable (fun w => 4 * c ^ 2 * (μ₁ w - g₁ w) ^ 2) ν :=
    hb₁.integrable_sq.const_mul _
  have hi₀ : Integrable (fun w => 4 * c ^ 2 * (μ₀ w - g₀ w) ^ 2) ν :=
    hb₀.integrable_sq.const_mul _
  have hj₁ : Integrable (fun w => 4 * κ ^ 2 * ((Y₁ w - μ₁ w) ^ 2 * (es w - e w) ^ 2)) ν :=
    (hUa hU₁).const_mul _
  have hj₀ : Integrable (fun w => 4 * κ ^ 2 * ((Y₀ w - μ₀ w) ^ 2 * (es w - e w) ^ 2)) ν :=
    (hUa hU₀).const_mul _
  have hκ2 : 0 ≤ 4 * κ ^ 2 := by positivity
  calc ∫ w, (aipwScoreOfSigma T Y e g₀ g₁ w - aipwScoreOfSigma T Y es μ₀ μ₁ w) ^ 2 ∂ν
      ≤ ∫ w, (4 * c ^ 2 * (μ₁ w - g₁ w) ^ 2 + 4 * c ^ 2 * (μ₀ w - g₀ w) ^ 2 +
          4 * κ ^ 2 * ((Y₁ w - μ₁ w) ^ 2 * (es w - e w) ^ 2) +
            4 * κ ^ 2 * ((Y₀ w - μ₀ w) ^ 2 * (es w - e w) ^ 2)) ∂ν :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
          (((hi₁.add hi₀).add hj₁).add hj₀) hpt
    _ = 4 * c ^ 2 * ∫ w, (μ₁ w - g₁ w) ^ 2 ∂ν + 4 * c ^ 2 * ∫ w, (μ₀ w - g₀ w) ^ 2 ∂ν +
          4 * κ ^ 2 * ∫ w, (Y₁ w - μ₁ w) ^ 2 * (es w - e w) ^ 2 ∂ν +
            4 * κ ^ 2 * ∫ w, (Y₀ w - μ₀ w) ^ 2 * (es w - e w) ^ 2 ∂ν := by
        rw [integral_add ?_ hj₀, integral_add ?_ hj₁, integral_add hi₁ hi₀, integral_const_mul,
          integral_const_mul, integral_const_mul, integral_const_mul]
        · exact hi₁.add hi₀
        · exact (hi₁.add hi₀).add hj₁
    _ ≤ 4 * c ^ 2 * ∫ w, (μ₁ w - g₁ w) ^ 2 ∂ν + 4 * c ^ 2 * ∫ w, (μ₀ w - g₀ w) ^ 2 ∂ν +
          4 * κ ^ 2 * (C * ∫ w, (es w - e w) ^ 2 ∂ν) +
            4 * κ ^ 2 * (C * ∫ w, (es w - e w) ^ 2 ∂ν) := by
        gcongr
        · exact hcU hU₁ hvar₁
        · exact hcU hU₀ hvar₀
    _ = _ := by ring

end ScoreError

section Asymptotic

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} {m : MeasurableSpace 𝒲} [m𝒲 : MeasurableSpace 𝒲]
  {P : Measure Ω} {ν : Measure 𝒲} [IsProbabilityMeasure ν]

/-- Eventual domination by a sequence tending to `0` in probability. -/
private lemma tendstoInMeasure_zero_of_eventually_abs_le {f g : ℕ → Ω → ℝ}
    (hg : TendstoInMeasure P g atTop 0) (hfg : ∀ᶠ n in atTop, ∀ ω, |f n ω| ≤ |g n ω|) :
    TendstoInMeasure P f atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hg ⊢
  intro δ hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hg δ hδ)
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hfg] with n hn
  refine measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω ⊢
  exact hω.trans (hn ω)

/-- A sum of two sequences tending to `0` in probability tends to `0` in probability. -/
private lemma tendstoInMeasure_add_zero' {f g : ℕ → Ω → ℝ} (hf : TendstoInMeasure P f atTop 0)
    (hg : TendstoInMeasure P g atTop 0) :
    TendstoInMeasure P (fun n ω => f n ω + g n ω) atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  intro δ hδ
  have h2 := (hf (δ / 2) (by positivity)).add (hg (δ / 2) (by positivity))
  rw [add_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => zero_le)
    fun n => (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs, Set.mem_union]
    at hω ⊢
  rcases le_or_gt (δ / 2) |f n ω| with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith [abs_add_le (f n ω) (g n ω)])

/-- A constant multiple of a sequence tending to `0` in probability tends to `0`. -/
private lemma tendstoInMeasure_const_mul_zero' (c : ℝ) {f : ℕ → Ω → ℝ}
    (hf : TendstoInMeasure P f atTop 0) : TendstoInMeasure P (fun n ω => c * f n ω) atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hf ⊢
  intro δ hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hf (δ / (|c| + 1)) (by positivity)) (fun _ => zero_le) fun n => measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs, abs_mul] at hω ⊢
  rw [div_le_iff₀ (by positivity)]
  nlinarith [abs_nonneg (f n ω), abs_nonneg c]

/-- **Nuisance consistency gives score consistency.** Under consistency, square integrable
potential outcomes, strong overlap and bounded conditional outcome variances, if for each fold
the fitted propensity and outcome regressions are `L²`-consistent in probability over the
training sample, `‖e* - ê‖₂² → 0`, `‖μ₁* - ĝ₁‖₂² → 0` and `‖μ₀* - ĝ₀‖₂² → 0`, then the fitted
AIPW score is `L²`-consistent for the oracle score: this is the hypothesis `hL2` of
`CrossFitting.tendstoInDistribution_crossFit_aipw`. The bound is
`integral_sq_aipwScoreOfSigma_sub_le`. -/
theorem tendstoInMeasure_integral_sq_crossFit_aipw_sub {W : ℕ → Ω → 𝒲} (hm : m ≤ m𝒲)
    {T : Set 𝒲} {Y Y₀ Y₁ : 𝒲 → ℝ} (hcons : Y =ᵐ[ν] observed T Y₀ Y₁)
    (hY₀ : MemLp Y₀ 2 ν) (hY₁ : MemLp Y₁ 2 ν) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hpos : ∀ᵐ w ∂ν, ε₀ ≤ ν[T.indicator 1 | m] w ∧ ν[T.indicator 1 | m] w ≤ 1 - ε₀) {C : ℝ}
    (hvar₀ : ν[fun w => (Y₀ w - ν[Y₀ | m] w) ^ 2 | m] ≤ᵐ[ν] fun _ => C)
    (hvar₁ : ν[fun w => (Y₁ w - ν[Y₁ | m] w) ^ 2 | m] ≤ᵐ[ν] fun _ => C)
    {K : ℕ} (fold : ℕ → ℕ → Fin K)
    {ê ĝ₀ ĝ₁ : (n : ℕ) → (k : Fin K) → (trainFold fold n k → 𝒲) → 𝒲 → ℝ}
    (hêσ : ∀ n k u, StronglyMeasurable[m] (ê n k u))
    (hĝ₀2 : ∀ n k u, MemLp (ĝ₀ n k u) 2 ν) (hĝ₁2 : ∀ n k u, MemLp (ĝ₁ n k u) 2 ν)
    {ε : ℝ} (hε : 0 < ε) (hêε : ∀ n k u w, ε ≤ ê n k u w ∧ ê n k u w ≤ 1 - ε)
    (hconₑ : ∀ k, TendstoInMeasure P (fun n ω =>
      ∫ w, (ν[T.indicator 1 | m] w - ê n k (trainData W fold n k ω) w) ^ 2 ∂ν) atTop 0)
    (hcon₀ : ∀ k, TendstoInMeasure P (fun n ω =>
      ∫ w, (ν[Y₀ | m] w - ĝ₀ n k (trainData W fold n k ω) w) ^ 2 ∂ν) atTop 0)
    (hcon₁ : ∀ k, TendstoInMeasure P (fun n ω =>
      ∫ w, (ν[Y₁ | m] w - ĝ₁ n k (trainData W fold n k ω) w) ^ 2 ∂ν) atTop 0) :
    ∀ k, TendstoInMeasure P (fun n ω => ∫ w,
      (aipwScoreOfSigma T Y (ê n k (trainData W fold n k ω)) (ĝ₀ n k (trainData W fold n k ω))
          (ĝ₁ n k (trainData W fold n k ω)) w -
        aipwScoreOfSigma T Y ν[T.indicator 1 | m] ν[Y₀ | m] ν[Y₁ | m] w) ^ 2 ∂ν) atTop 0 := by
  intro k
  have hg := tendstoInMeasure_add_zero'
    (tendstoInMeasure_const_mul_zero' (4 * (1 + ε⁻¹) ^ 2)
      (tendstoInMeasure_add_zero' (hcon₁ k) (hcon₀ k)))
    (tendstoInMeasure_const_mul_zero' (8 * C * (ε⁻¹ * ε₀⁻¹) ^ 2) (hconₑ k))
  refine tendstoInMeasure_zero_of_eventually_abs_le hg (Eventually.of_forall fun n ω => ?_)
  set u := trainData W fold n k ω
  rw [abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
  exact (integral_sq_aipwScoreOfSigma_sub_le hm hcons hY₀ hY₁ hε₀ hpos hvar₀ hvar₁ (hêσ n k u)
    (hĝ₀2 n k u) (hĝ₁2 n k u) hε (ae_of_all _ (hêε n k u))).trans (le_abs_self _)

variable [IsProbabilityMeasure P]

/-- **Double/debiased machine learning under rate conditions**, an analogue of Chernozhukov et
al. (2018, Theorem 5.1) for the ATE with the potential-outcome variance bound of
`integral_sq_aipwScoreOfSigma_sub_le` in place of the paper's noise condition. `W 0, W 1, …`
are i.i.d. full-data observations with law `ν`; `T` is the treatment event,
`Y = observed T Y₀ Y₁` the observed outcome, `m` the covariate σ-algebra,
`e* = P(T | m)`, `μₐ* = E[Yₐ | m]`. Assume mean exchangeability, strong overlap
`ε₀ ≤ e* ≤ 1 - ε₀`, square integrable potential outcomes with bounded conditional variances
`E[(Yₐ - μₐ*)² | m] ≤ C`, and fitted nuisances `ê, ĝ₀, ĝ₁` for each fold that depend only on that
fold's training data, are `m`-measurable, square integrable and clipped to `[ε, 1 - ε]`. If, for
each fold,
* the fitted nuisances are `L²`-consistent in probability:
  `‖e* - ê‖₂ → 0`, `‖μ₀* - ĝ₀‖₂ → 0`, `‖μ₁* - ĝ₁‖₂ → 0` (stated for the squared norms), and
* the product of nuisance errors is `o_P(n^{-1/2})`:
  `√n ‖e* - ê‖₂ (‖μ₁* - ĝ₁‖₂ + ‖μ₀* - ĝ₀‖₂) → 0` in probability,

then `√n (τ̂ₙ - E[Y₁ - Y₀]) → N(0, Var ψ*)` in distribution, where `τ̂ₙ` is the cross-fitted
AIPW estimator and `ψ* = ψ(e*, μ₀*, μ₁*)` the oracle score. Unlike
`CrossFitting.tendstoInDistribution_crossFit_aipw`, no condition on the fitted score is
assumed. -/
theorem tendstoInDistribution_crossFit_aipw_of_rates {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {W : ℕ → Ω → 𝒲} (hW : ∀ i, Measurable (W i))
    (hindep : iIndepFun W P) (hident : ∀ i, IdentDistrib (W i) (W 0) P P)
    (hν : P.map (W 0) = ν) (hm : m ≤ m𝒲) {T : Set 𝒲} (hT : MeasurableSet T)
    {Y Y₀ Y₁ : 𝒲 → ℝ} (hY : Measurable Y) (hcons : Y =ᵐ[ν] observed T Y₀ Y₁)
    (hY₀ : MemLp Y₀ 2 ν) (hY₁ : MemLp Y₁ 2 ν)
    (hex₁ : ν[T.indicator Y₁ | m] =ᵐ[ν] ν[T.indicator 1 | m] * ν[Y₁ | m])
    (hex₀ : ν[Tᶜ.indicator Y₀ | m] =ᵐ[ν] (1 - ν[T.indicator 1 | m]) * ν[Y₀ | m])
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hpos : ∀ᵐ w ∂ν, ε₀ ≤ ν[T.indicator 1 | m] w ∧ ν[T.indicator 1 | m] w ≤ 1 - ε₀) {C : ℝ}
    (hvar₀ : ν[fun w => (Y₀ w - ν[Y₀ | m] w) ^ 2 | m] ≤ᵐ[ν] fun _ => C)
    (hvar₁ : ν[fun w => (Y₁ w - ν[Y₁ | m] w) ^ 2 | m] ≤ᵐ[ν] fun _ => C)
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
    (hconₑ : ∀ k, TendstoInMeasure P (fun n ω =>
      ∫ w, (ν[T.indicator 1 | m] w - ê n k (trainData W fold n k ω) w) ^ 2 ∂ν) atTop 0)
    (hcon₀ : ∀ k, TendstoInMeasure P (fun n ω =>
      ∫ w, (ν[Y₀ | m] w - ĝ₀ n k (trainData W fold n k ω) w) ^ 2 ∂ν) atTop 0)
    (hcon₁ : ∀ k, TendstoInMeasure P (fun n ω =>
      ∫ w, (ν[Y₁ | m] w - ĝ₁ n k (trainData W fold n k ω) w) ^ 2 ∂ν) atTop 0)
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
          ∫ w, (Y₁ w - Y₀ w) ∂ν)) atTop Z (fun _ => P) P' :=
  tendstoInDistribution_crossFit_aipw hW hindep hident hν hm hT hY hcons hY₀ hY₁ hex₁ hex₀ hε₀
    hpos fold hêm hĝ₀m hĝ₁m hêσ hĝ₀σ hĝ₁σ hĝ₀2 hĝ₁2 hε hêε
    (tendstoInMeasure_integral_sq_crossFit_aipw_sub hm hcons hY₀ hY₁ hε₀ hpos hvar₀ hvar₁ fold
      hêσ hĝ₀2 hĝ₁2 hε hêε hconₑ hcon₀ hcon₁) hrate hZ

/-- `√a √b ≤ (a + b) / 2` summed over two outcome arms. -/
private lemma sqrt_mul_add_sqrt_le {a b₁ b₀ : ℝ} (ha : 0 ≤ a) (hb₁ : 0 ≤ b₁) (hb₀ : 0 ≤ b₀) :
    √a * (√b₁ + √b₀) ≤ a + b₁ + b₀ := by
  nlinarith [sq_nonneg (√a - √b₁), sq_nonneg (√a - √b₀), Real.sq_sqrt ha, Real.sq_sqrt hb₁,
    Real.sq_sqrt hb₀, Real.sqrt_nonneg b₁, Real.sqrt_nonneg b₀]

/-- **Each nuisance at rate `o_P(n^{-1/4})` suffices.** Under the hypotheses of
`tendstoInDistribution_crossFit_aipw_of_rates` without its consistency and product-rate
conditions, if for each fold `√n ‖e* - ê‖₂² → 0`, `√n ‖μ₀* - ĝ₀‖₂² → 0` and
`√n ‖μ₁* - ĝ₁‖₂² → 0` in probability (each nuisance converges in `L²` faster than `n^{-1/4}`),
then `√n (τ̂ₙ - E[Y₁ - Y₀]) → N(0, Var ψ*)` in distribution. Consistency follows because
`‖·‖₂² ≤ √n ‖·‖₂²` for `n ≥ 1`, and the product rate because
`√n ‖a‖ (‖b₁‖ + ‖b₀‖) ≤ √n (‖a‖² + ‖b₁‖² + ‖b₀‖²)`. -/
theorem tendstoInDistribution_crossFit_aipw_of_quarter_rates {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P'] {W : ℕ → Ω → 𝒲}
    (hW : ∀ i, Measurable (W i)) (hindep : iIndepFun W P)
    (hident : ∀ i, IdentDistrib (W i) (W 0) P P) (hν : P.map (W 0) = ν) (hm : m ≤ m𝒲)
    {T : Set 𝒲} (hT : MeasurableSet T) {Y Y₀ Y₁ : 𝒲 → ℝ} (hY : Measurable Y)
    (hcons : Y =ᵐ[ν] observed T Y₀ Y₁) (hY₀ : MemLp Y₀ 2 ν) (hY₁ : MemLp Y₁ 2 ν)
    (hex₁ : ν[T.indicator Y₁ | m] =ᵐ[ν] ν[T.indicator 1 | m] * ν[Y₁ | m])
    (hex₀ : ν[Tᶜ.indicator Y₀ | m] =ᵐ[ν] (1 - ν[T.indicator 1 | m]) * ν[Y₀ | m])
    {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hpos : ∀ᵐ w ∂ν, ε₀ ≤ ν[T.indicator 1 | m] w ∧ ν[T.indicator 1 | m] w ≤ 1 - ε₀) {C : ℝ}
    (hvar₀ : ν[fun w => (Y₀ w - ν[Y₀ | m] w) ^ 2 | m] ≤ᵐ[ν] fun _ => C)
    (hvar₁ : ν[fun w => (Y₁ w - ν[Y₁ | m] w) ^ 2 | m] ≤ᵐ[ν] fun _ => C)
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
    (hqₑ : ∀ k, TendstoInMeasure P (fun (n : ℕ) ω => √(n : ℝ) *
      ∫ w, (ν[T.indicator 1 | m] w - ê n k (trainData W fold n k ω) w) ^ 2 ∂ν) atTop 0)
    (hq₀ : ∀ k, TendstoInMeasure P (fun (n : ℕ) ω => √(n : ℝ) *
      ∫ w, (ν[Y₀ | m] w - ĝ₀ n k (trainData W fold n k ω) w) ^ 2 ∂ν) atTop 0)
    (hq₁ : ∀ k, TendstoInMeasure P (fun (n : ℕ) ω => √(n : ℝ) *
      ∫ w, (ν[Y₁ | m] w - ĝ₁ n k (trainData W fold n k ω) w) ^ 2 ∂ν) atTop 0)
    {Z : Ω' → ℝ} (hZ : HasLaw Z
      (gaussianReal 0
        Var[aipwScoreOfSigma T Y ν[T.indicator 1 | m] ν[Y₀ | m] ν[Y₁ | m]; ν].toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) *
      (crossFitEstimator W fold (fun n k z =>
        aipwScoreOfSigma T Y (ê n k z.1) (ĝ₀ n k z.1) (ĝ₁ n k z.1) z.2) n ω -
          ∫ w, (Y₁ w - Y₀ w) ∂ν)) atTop Z (fun _ => P) P' := by
  -- `‖·‖₂² ≤ √n ‖·‖₂²` once `n ≥ 1`.
  have hcon : ∀ {f : ℕ → Ω → 𝒲 → ℝ}, TendstoInMeasure P (fun (n : ℕ) ω => √(n : ℝ) *
      ∫ w, f n ω w ^ 2 ∂ν) atTop 0 →
      TendstoInMeasure P (fun n ω => ∫ w, f n ω w ^ 2 ∂ν) atTop 0 := by
    intro f hf
    refine tendstoInMeasure_zero_of_eventually_abs_le hf ?_
    filter_upwards [eventually_ge_atTop 1] with n hn ω
    have hI : 0 ≤ ∫ w, f n ω w ^ 2 ∂ν := integral_nonneg fun _ => sq_nonneg _
    have hs : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast hn)
    rw [abs_of_nonneg hI, abs_of_nonneg (by positivity)]
    nlinarith
  refine tendstoInDistribution_crossFit_aipw_of_rates hW hindep hident hν hm hT hY hcons hY₀ hY₁
    hex₁ hex₀ hε₀ hpos hvar₀ hvar₁ fold hêm hĝ₀m hĝ₁m hêσ hĝ₀σ hĝ₁σ hĝ₀2 hĝ₁2 hε hêε
    (fun k => hcon (hqₑ k)) (fun k => hcon (hq₀ k)) (fun k => hcon (hq₁ k)) (fun k => ?_) hZ
  refine tendstoInMeasure_zero_of_eventually_abs_le
    (tendstoInMeasure_add_zero' (tendstoInMeasure_add_zero' (hqₑ k) (hq₁ k)) (hq₀ k))
    (Eventually.of_forall fun n ω => ?_)
  set u := trainData W fold n k ω
  have ha : 0 ≤ ∫ w, (ν[T.indicator 1 | m] w - ê n k u w) ^ 2 ∂ν :=
    integral_nonneg fun _ => sq_nonneg _
  have hb₁ : 0 ≤ ∫ w, (ν[Y₁ | m] w - ĝ₁ n k u w) ^ 2 ∂ν := integral_nonneg fun _ => sq_nonneg _
  have hb₀ : 0 ≤ ∫ w, (ν[Y₀ | m] w - ĝ₀ n k u w) ^ 2 ∂ν := integral_nonneg fun _ => sq_nonneg _
  have hs : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_left (sqrt_mul_add_sqrt_le ha hb₁ hb₀) hs
  linarith

end Asymptotic

end MathlibExt.Probability.Causality.AugmentedIPW.DoubleMLRates
