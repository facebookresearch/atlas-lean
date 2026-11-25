/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import MathlibExt.Probability.Causality.MissingData.GaussianSelection
public import MathlibExt.Probability.Statistics.StandardizedSelection
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.Integration
import MathlibExt.Probability.Distributions.GaussianCdf

/-!
# Truncation selection on Gaussian scores

For a score `I` with a Gaussian law and positive variance, selecting the outcomes at least `z`
standard deviations above the mean (the standardized upper event of
`MathlibExt.Probability.Statistics.StandardizedSelection`) keeps the proportion `Φ(-z)`, the
standard normal upper tail, and raises the mean of the standardized score by the inverse Mills
ratio `φ(z) / Φ(-z)` (the intensity of selection). If `(H, I)` is jointly Gaussian, the mean of
`H` shifts by `inverseMillsRatio (-z) * cov[I, H] / σ_I`, so it does not move when `H` and `I`
are uncorrelated.

## Main results

* `hasLaw_standardizedValue`: a standardized Gaussian score is standard normal.
* `measureReal_standardizedUpperEvent`, `gaussianUpperTail_mem_Ioo`: the selected proportion.
* `integral_cond_standardizedValue`, `inverseMillsRatio_neg_eq_pdf_div_upperTail`: the
  intensity of selection.
* `conditionalMeanShift_standardizedUpperEvent_gaussian`: the response of a jointly Gaussian
  quantity.
* `conditionalMeanShift_eq_zero_of_covariance_eq_zero`,
  `conditionalMeanShift_linear_eq_zero_of_crossCovariance_eq_zero`: no response without
  covariance.

## References

* L. N. Hazel, *The genetic basis for constructing selection indexes*, Genetics 28 (1943)
  476–490.
* J. J. Heckman, *Sample selection bias as a specification error*, Econometrica 47 (1979)
  153–161.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open MathlibExt.Probability.Causality.MissingData (inverseMillsRatio)

namespace ProbabilityTheory

/-- **Standardizing a Gaussian score.** Let `μ` be a measure on `Ω` and `f : Ω → ℝ` a random
variable with a Gaussian law under `μ` (`HasGaussianLaw f μ`) and `Var[f; μ] > 0`. Then the
standardized score `standardizedValue μ f = (f - μ[f]) / populationSD μ f` has the standard
normal law `gaussianReal 0 1` under `μ`. -/
theorem hasLaw_standardizedValue {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (_hf : HasGaussianLaw f μ) (_hvar : 0 < Var[f; μ]) :
    HasLaw (standardizedValue μ f) (gaussianReal 0 1) μ := by
  have hv : (Var[f; μ].toNNReal : ℝ) = Var[f; μ] :=
    Real.coe_toNNReal _ _hvar.le
  have hne : Var[f; μ].toNNReal ≠ 0 := by
    intro h
    have hzero := congrArg (fun x : NNReal => (x : ℝ)) h
    rw [hv] at hzero
    exact _hvar.ne' hzero
  have hsq : ∀ h : 0 ≤ populationSD μ f ^ 2,
      NNReal.mk (populationSD μ f ^ 2) h = Var[f; μ].toNNReal := by
    intro h
    apply Subtype.ext
    exact (Real.sq_sqrt _hvar.le).trans hv.symm
  have hsub : Measurable (fun y : ℝ => y - μ[f]) := measurable_id.sub_const _
  have hdiv : Measurable (fun y : ℝ => y / populationSD μ f) :=
    measurable_id.div_const _
  have hg : HasLaw (fun y : ℝ => (y - μ[f]) / populationSD μ f)
      (gaussianReal 0 1) (gaussianReal μ[f] Var[f; μ].toNNReal) := by
    refine ⟨((measurable_id.sub_const _).div_const _).aemeasurable, ?_⟩
    rw [show (fun y : ℝ => (y - μ[f]) / populationSD μ f) =
        (fun y : ℝ => y / populationSD μ f) ∘ (fun y : ℝ => y - μ[f]) from rfl,
      ← Measure.map_map hdiv hsub,
      gaussianReal_map_sub_const, gaussianReal_map_div_const,
      sub_self, zero_div, hsq _, div_self hne]
  exact hg.fun_comp ⟨_hf.aemeasurable, _hf.map_eq_gaussianReal⟩

/-- **The selected proportion of a Gaussian score.** Let `μ` be a probability measure on `Ω`,
`f : Ω → ℝ` a random variable with a Gaussian law under `μ` and `Var[f; μ] > 0`, and `z ∈ ℝ`.
Then the probability of the standardized upper event `{ω | μ[f] + z σ_f ≤ f ω}` is the standard
normal upper tail at `z`, written `Φ(-z) = cdf (gaussianReal 0 1) (-z)`. -/
theorem measureReal_standardizedUpperEvent {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (_hf : HasGaussianLaw f μ)
    (_hvar : 0 < Var[f; μ]) (z : ℝ) :
    μ.real (standardizedUpperEvent μ f z) = cdf (gaussianReal 0 1) (-z) := by
  have hsd : 0 < populationSD μ f := Real.sqrt_pos.mpr _hvar
  have hevent : standardizedUpperEvent μ f z =
      {ω | -(-z) ≤ standardizedValue μ f ω} := by
    ext ω
    simp only [standardizedUpperEvent, Set.mem_ofPred_eq, standardizedValue, neg_neg]
    rw [le_div_iff₀ hsd]
    constructor <;> intro h <;> linarith
  rw [hevent]
  exact MathlibExt.Probability.Causality.MissingData.measureReal_selection_eq_cdf
    (hasLaw_standardizedValue _hf _hvar)

/-- **Every finite threshold selects a proper fraction.** For every real `z`, the standard normal
upper tail `Φ(-z) = cdf (gaussianReal 0 1) (-z)` lies in the open interval `(0, 1)`. -/
theorem gaussianUpperTail_mem_Ioo (z : ℝ) :
    cdf (gaussianReal 0 1) (-z) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpos : ∀ x : ℝ, 0 < cdf (gaussianReal 0 1) x := by
    intro x
    exact (cdf_nonneg (gaussianReal 0 1) (x - 1)).trans_lt
      (strictMono_cdf_gaussianReal 0 one_ne_zero (by linarith : x - 1 < x))
  refine ⟨hpos (-z), ?_⟩
  rw [cdf_gaussianReal_neg]
  linarith [hpos z]

/-- **Selected mean of a standardized Gaussian score.** Let `μ` be a probability measure on `Ω`,
`f : Ω → ℝ` a measurable random variable with a Gaussian law under `μ` and `Var[f; μ] > 0`, and
`z ∈ ℝ`. Then the mean of the standardized score `standardizedValue μ f` under the conditional
measure of the standardized upper event at `z` equals the inverse Mills ratio at `-z`,
`inverseMillsRatio (-z) = φ(z) / Φ(-z)`. -/
theorem integral_cond_standardizedValue {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (_hfmeas : Measurable f)
    (_hf : HasGaussianLaw f μ) (_hvar : 0 < Var[f; μ]) (z : ℝ) :
    (∫ ω, standardizedValue μ f ω ∂μ[|standardizedUpperEvent μ f z]) =
      inverseMillsRatio (-z) := by
  have hsd : 0 < populationSD μ f := Real.sqrt_pos.mpr _hvar
  have hevent : standardizedUpperEvent μ f z =
      {ω | -(-z) ≤ standardizedValue μ f ω} := by
    ext ω
    simp only [standardizedUpperEvent, Set.mem_ofPred_eq, standardizedValue, neg_neg]
    rw [le_div_iff₀ hsd]
    constructor <;> intro h <;> linarith
  rw [hevent]
  exact MathlibExt.Probability.Causality.MissingData.integral_cond_selectionError_eq
    (hasLaw_standardizedValue _hf _hvar) ((_hfmeas.sub_const _).div_const _)

/-- **The intensity of selection in upper-tail notation.** For every real `z`,
`inverseMillsRatio (-z) = φ(z) / Φ(-z)`, where `φ = gaussianPDFReal 0 1` is the standard normal
density and `Φ(-z) = cdf (gaussianReal 0 1) (-z)` is the standard normal upper tail at `z`. -/
theorem inverseMillsRatio_neg_eq_pdf_div_upperTail (z : ℝ) :
    inverseMillsRatio (-z) = gaussianPDFReal 0 1 z / cdf (gaussianReal 0 1) (-z) := by
  simp [inverseMillsRatio, gaussianPDFReal_def]

/-- **Response to truncation selection on a Gaussian score.** Let `μ` be a probability measure
on `Ω`, and `H, I : Ω → ℝ` random variables with `I` measurable, `(H, I)` jointly Gaussian under
`μ` (`HasGaussianLaw (fun ω => (H ω, I ω)) μ`) and `Var[I; μ] > 0`. Then for every threshold
`z ∈ ℝ`, selecting the standardized upper event of `I` at `z` shifts the mean of `H` by
`inverseMillsRatio (-z) * (cov[I, H; μ] / populationSD μ I)`. -/
theorem conditionalMeanShift_standardizedUpperEvent_gaussian {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {H I : Ω → ℝ} (_hI : Measurable I)
    (_hHI : HasGaussianLaw (fun ω => (H ω, I ω)) μ) (_hvar : 0 < Var[I; μ]) (z : ℝ) :
    conditionalMeanShift μ H (standardizedUpperEvent μ I z) =
      inverseMillsRatio (-z) * (cov[I, H; μ] / populationSD μ I) := by
  classical
  let β : ℝ := cov[I, H; μ] / Var[I; μ]
  let R : Ω → ℝ := fun ω => H ω - β * I ω
  let s := standardizedUpperEvent μ I z
  have hIR : HasGaussianLaw (fun ω => (I ω, R ω)) μ := by
    let p := ContinuousLinearMap.fst ℝ ℝ ℝ
    let q := ContinuousLinearMap.snd ℝ ℝ ℝ
    exact _hHI.map_fun (q.prod (p - β • q))
  have hcov : cov[I, R; μ] = 0 := by
    dsimp [R]
    rw [covariance_fun_sub_right _hHI.snd.memLp_two _hHI.fst.memLp_two
      (_hHI.snd.memLp_two.const_mul β), covariance_const_mul_right,
      covariance_self _hHI.snd.aemeasurable]
    dsimp [β]
    field_simp
    ring
  have hind : IndepFun I R μ := hIR.indepFun_of_covariance_eq_zero hcov
  have hs : MeasurableSet s := measurableSet_le measurable_const _hI
  have hpos : 0 < μ.real s := by
    rw [measureReal_standardizedUpperEvent _hHI.snd _hvar]
    exact (gaussianUpperTail_mem_Ioo z).1
  have hμpos : 0 < μ s := (ENNReal.toReal_pos_iff.mp hpos).1
  have hne : μ s ≠ 0 := hμpos.ne'
  have : IsProbabilityMeasure μ[|s] := cond_isProbabilityMeasure hne
  have hH : Integrable H μ[|s] :=
    _hHI.fst.integrable.restrict.smul_measure (ENNReal.inv_ne_top.mpr hne)
  have hI : Integrable I μ[|s] :=
    _hHI.snd.integrable.restrict.smul_measure (ENNReal.inv_ne_top.mpr hne)
  have hR : conditionalMeanShift μ R s = 0 := by
    let t := Set.Ici (μ[I] + z * populationSD μ I)
    have ht : MeasurableSet t := measurableSet_Ici
    have hf : AEStronglyMeasurable (t.indicator (fun _ : ℝ => (1 : ℝ)))
        (μ.map I) := (measurable_const.indicator ht).aestronglyMeasurable
    have hg : AEStronglyMeasurable (id : ℝ → ℝ) (μ.map R) :=
      measurable_id.aestronglyMeasurable
    have hfac := hind.integral_fun_comp_mul_comp hIR.fst.aemeasurable
      hIR.snd.aemeasurable hf hg
    have hfun : (fun ω => t.indicator (fun _ => (1 : ℝ)) (I ω)) =
        s.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases h : ω ∈ s <;> simp [t, s, standardizedUpperEvent] at h ⊢ <;> simp [h]
    change (∫ ω, t.indicator (fun _ => (1 : ℝ)) (I ω) * R ω ∂μ) =
      (∫ ω, t.indicator (fun _ => (1 : ℝ)) (I ω) ∂μ) * μ[R] at hfac
    have hmul : (fun ω => t.indicator (fun _ => (1 : ℝ)) (I ω) * R ω) =
        fun ω => s.indicator (fun _ => (1 : ℝ)) ω * R ω := by
      funext ω
      rw [← hfun]
    rw [hmul, hfun] at hfac
    rw [conditionalMeanShift_eq_indicator_quotient hs hμpos, hfac]
    have hden : (∫ ω, s.indicator (fun _ => (1 : ℝ)) ω ∂μ) ≠ 0 := by
      simpa [integral_indicator hs, setIntegral_const] using hpos.ne'
    field_simp
    ring
  have hstd := integral_cond_standardizedValue _hI _hHI.snd _hvar z
  change (∫ ω, (I ω - μ[I]) / populationSD μ I ∂μ[|s]) =
    inverseMillsRatio (-z) at hstd
  rw [integral_div, integral_sub hI (integrable_const _)] at hstd
  simp only [integral_const] at hstd
  simp only [Measure.real_def, measure_univ, ENNReal.toReal_one, one_smul] at hstd
  change (∫ ω, H ω - β * I ω ∂μ[|s]) -
    (∫ ω, H ω - β * I ω ∂μ) = 0 at hR
  rw [integral_sub hH (hI.const_mul β), integral_const_mul,
    integral_sub _hHI.fst.integrable (_hHI.snd.integrable.const_mul β),
    integral_const_mul] at hR
  have hsd : populationSD μ I ≠ 0 := (Real.sqrt_pos.mpr _hvar).ne'
  have hsq : populationSD μ I ^ 2 = Var[I; μ] := Real.sq_sqrt _hvar.le
  unfold conditionalMeanShift
  change (∫ ω, H ω ∂μ[|s]) - μ[H] = _
  have hshift : (∫ ω, I ω ∂μ[|s]) - μ[I] =
      inverseMillsRatio (-z) * populationSD μ I := (div_eq_iff hsd).mp hstd
  calc
    _ = β * ((∫ ω, I ω ∂μ[|s]) - μ[I]) := by linarith
    _ = inverseMillsRatio (-z) * (cov[I, H; μ] / populationSD μ I) := by
      rw [hshift]
      dsimp [β]
      rw [← hsq]
      field_simp

/-- **Zero covariance gives zero response.** Let `μ` be a probability measure on `Ω`, and
`H, I : Ω → ℝ` random variables with `I` measurable, `(H, I)` jointly Gaussian under `μ`,
`Var[I; μ] > 0` and `cov[I, H; μ] = 0`. Then for every threshold `z ∈ ℝ`, selecting the
standardized upper event of `I` at `z` does not change the mean of `H`: the conditional mean
shift is `0`. -/
theorem conditionalMeanShift_eq_zero_of_covariance_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {H I : Ω → ℝ} (_hI : Measurable I)
    (_hHI : HasGaussianLaw (fun ω => (H ω, I ω)) μ) (_hvar : 0 < Var[I; μ])
    (_hcov : cov[I, H; μ] = 0) (z : ℝ) :
    conditionalMeanShift μ H (standardizedUpperEvent μ I z) = 0 := by
  rw [conditionalMeanShift_standardizedUpperEvent_gaussian _hI _hHI _hvar]
  simp [_hcov]

/-- **Zero cross-covariance gives zero response for every linear score.** Let `μ` be a
probability measure on `Ω`, `X : Ω → ℝⁿ` a measurable random vector and `H : Ω → ℝ` with `(X, H)`
jointly Gaussian under `μ`, the covariance matrix `(cov[X_i, X_j; μ])` positive definite, and
`cov[X_i, H; μ] = 0` for every `i`. Then for every nonzero `b ∈ ℝⁿ` and every threshold `z ∈ ℝ`,
selecting the standardized upper event of the score `b ⬝ᵥ X` at `z` does not change the mean of
`H`: the conditional mean shift is `0`. -/
theorem conditionalMeanShift_linear_eq_zero_of_crossCovariance_eq_zero
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → Fin n → ℝ} {H : Ω → ℝ} (_hX : Measurable X)
    (_hXH : HasGaussianLaw (fun ω => (X ω, H ω)) μ)
    (_hP : Matrix.PosDef (fun i j => cov[fun ω => X ω i, fun ω => X ω j; μ] :
      Matrix (Fin n) (Fin n) ℝ))
    (_hc : ∀ i, cov[fun ω => X ω i, H; μ] = 0) {b : Fin n → ℝ} (_hb : b ≠ 0) (z : ℝ) :
    conditionalMeanShift μ H (standardizedUpperEvent μ (fun ω => b ⬝ᵥ X ω) z) = 0 := by
  let c : (Fin n → ℝ) →L[ℝ] ℝ :=
    ∑ i, b i • ContinuousLinearMap.proj i
  let p := ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ
  let q := ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ
  have hHI : HasGaussianLaw (fun ω => (H ω, b ⬝ᵥ X ω)) μ := by
    simpa [c, p, q, dotProduct, _root_.sum_apply] using
      _hXH.map_fun (q.prod (c.comp p))
  have hXm : ∀ i, MemLp (fun ω => X ω i) 2 μ := fun i =>
    (_hXH.fst.eval i).memLp_two
  apply conditionalMeanShift_eq_zero_of_covariance_eq_zero
  · change Measurable (fun ω => ∑ i, b i * X ω i)
    exact Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((measurable_pi_apply i).comp _hX)
  · exact hHI
  · rw [← covariance_self hHI.snd.aemeasurable,
      covariance_dotProduct_dotProduct hXm hXm]
    exact _hP.dotProduct_mulVec_pos _hb
  · rw [covariance_dotProduct_left hXm _hXH.snd.memLp_two]
    simp [_hc]

end ProbabilityTheory
