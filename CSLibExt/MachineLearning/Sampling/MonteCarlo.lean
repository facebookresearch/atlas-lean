/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.StrongLaw

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Monte Carlo and importance sampling

Estimate `∫ f dν` by averaging `f` over samples.

* `mcEstimate f X n`: the Monte Carlo average `(1 / n) ∑_{i < n} f (X i)`.
* `integral_mcEstimate` (**unbiased**): if every sample has law `ν`, the estimate has expectation
  `∫ f dν`.
* `tendsto_mcEstimate` (**consistent**): for pairwise independent samples it converges almost
  surely to `∫ f dν`. This is Mathlib's strong law of large numbers
  (`ProbabilityTheory.strong_law_ae`) applied to `f (X i)`.
* `isEstimate w f X n`: the **importance-sampling** average of `w (X i) f (X i)` with samples from a
  proposal `ρ` and target `ν = ρ.withDensity w`. `integral_weight_mul` is the change of measure,
  `integral_isEstimate` says the estimator is unbiased for `∫ f dν`, and `tendsto_isEstimate` that
  it is consistent. The `*_of_integrable` variants need only integrability of the integrand, and
  the `*_rnDeriv` variants take the target through its Radon–Nikodym derivative.

## References

* C. P. Robert and G. Casella, *Monte Carlo Statistical Methods*, 2nd ed., Springer, 2004, §3.2
  and §3.3.
* C. M. Bishop, *Pattern Recognition and Machine Learning*, Springer, 2006, §11.1.4.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Sampling

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω}

/-- The **Monte Carlo estimate** of `E[f(X)]` from the first `n` samples `X 0, …, X (n - 1)`:
`(1 / n) ∑ f (X i)`. -/
noncomputable def mcEstimate (f : α → ℝ) (X : ℕ → Ω → α) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ range n, f (X i ω)

/-- **The Monte Carlo estimator is unbiased**: if the samples have a common law `ν`, the estimate
from `n > 0` samples has expectation `∫ f dν`. -/
theorem integral_mcEstimate {ν : Measure α} {f : α → ℝ}
    (hf : Measurable f) (hfi : Integrable f ν) {X : ℕ → Ω → α} (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = ν) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, mcEstimate f X n ω ∂μ = ∫ x, f x ∂ν := by
  have hint : ∀ i, Integrable (fun ω ↦ f (X i ω)) μ := fun i ↦ by
    have := hfi
    rw [← hlaw i] at this
    exact this.comp_measurable (hX i)
  have heq : ∀ i, ∫ ω, f (X i ω) ∂μ = ∫ x, f x ∂ν := fun i ↦ by
    rw [← hlaw i, integral_map (hX i).aemeasurable hf.aestronglyMeasurable]
  simp only [mcEstimate]
  rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ hint i]
  simp only [heq, sum_const, card_range, nsmul_eq_mul]
  field_simp

/-- **The Monte Carlo estimator is consistent** (strong law of large numbers): for pairwise
independent samples with a common law `ν` and `f ∈ L¹(ν)`, the estimate converges almost surely
to `∫ f dν`. -/
theorem tendsto_mcEstimate {ν : Measure α} {f : α → ℝ}
    (hf : Measurable f) (hfi : Integrable f ν) {X : ℕ → Ω → α} (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = ν) (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ mcEstimate f X n ω) atTop (𝓝 (∫ x, f x ∂ν)) := by
  set Y : ℕ → Ω → ℝ := fun i ω ↦ f (X i ω) with hY
  have hint : Integrable (Y 0) μ := by
    have := hfi
    rw [← hlaw 0] at this
    exact this.comp_measurable (hX 0)
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := fun i ↦
    (IdentDistrib.mk (hX i).aemeasurable (hX 0).aemeasurable (by rw [hlaw i, hlaw 0])).comp hf
  have hind : Pairwise (Function.onFun (· ⟂ᵢ[μ] ·) Y) := fun i j hij ↦ (hindep hij).comp hf hf
  have hlim : ∫ ω, Y 0 ω ∂μ = ∫ x, f x ∂ν := by
    rw [hY, ← hlaw 0, integral_map (hX 0).aemeasurable hf.aestronglyMeasurable]
  filter_upwards [strong_law_ae Y hint hind hident] with ω hω
  rw [← hlim]
  simpa [mcEstimate, smul_eq_mul] using hω

/-! ### Importance sampling -/

/-- The **importance-sampling estimate** of `∫ f dν` from samples of a proposal `ρ`, where the
target is `ν = ρ.withDensity w`: the average of `w (X i) * f (X i)` over the first `n` samples. -/
noncomputable def isEstimate (w : α → ℝ≥0∞) (f : α → ℝ) (X : ℕ → Ω → α) (n : ℕ) (ω : Ω) : ℝ :=
  mcEstimate (fun x ↦ (w x).toReal * f x) X n ω

/-- The importance weight corrects the change of measure: `∫ w f dρ = ∫ f d(ρ.withDensity w)`. -/
theorem integral_weight_mul {ρ : Measure α} {w : α → ℝ≥0∞} (hw : Measurable w)
    (hwt : ∀ᵐ x ∂ρ, w x < ∞) (f : α → ℝ) :
    ∫ x, (w x).toReal * f x ∂ρ = ∫ x, f x ∂(ρ.withDensity w) :=
  (integral_withDensity_eq_integral_toReal_smul hw hwt f).symm

/-- **Importance sampling is unbiased**: with samples from the proposal `ρ` and target
`ν = ρ.withDensity w`, the estimate from `n > 0` samples has expectation `∫ f dν`. -/
theorem integral_isEstimate {ρ : Measure α} {w : α → ℝ≥0∞}
    (hw : Measurable w) (hwt : ∀ᵐ x ∂ρ, w x < ∞) {f : α → ℝ} (hf : Measurable f)
    (hfi : Integrable f (ρ.withDensity w)) {X : ℕ → Ω → α} (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = ρ) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, isEstimate w f X n ω ∂μ = ∫ x, f x ∂(ρ.withDensity w) := by
  rw [← integral_weight_mul hw hwt]
  exact integral_mcEstimate (hw.ennreal_toReal.mul hf)
    ((integrable_withDensity_iff_integrable_smul' hw hwt).mp hfi) hX hlaw hn

/-- **Importance sampling is consistent**: for pairwise independent samples from `ρ`, the estimate
converges almost surely to `∫ f d(ρ.withDensity w)`. -/
theorem tendsto_isEstimate {ρ : Measure α} {w : α → ℝ≥0∞}
    (hw : Measurable w) (hwt : ∀ᵐ x ∂ρ, w x < ∞) {f : α → ℝ} (hf : Measurable f)
    (hfi : Integrable f (ρ.withDensity w)) {X : ℕ → Ω → α} (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = ρ) (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ isEstimate w f X n ω) atTop
      (𝓝 (∫ x, f x ∂(ρ.withDensity w))) := by
  rw [← integral_weight_mul hw hwt]
  exact tendsto_mcEstimate (hw.ennreal_toReal.mul hf)
    ((integrable_withDensity_iff_integrable_smul' hw hwt).mp hfi) hX hlaw hindep

/-! ### Integrable-integrand helpers: the a.e.-modification argument for plain Monte Carlo -/

private theorem mcEstimate_ae_eq_aux {ν : Measure α} {f g : α → ℝ} (hfg : f =ᵐ[ν] g)
    {X : ℕ → Ω → α} (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, μ.map (X i) = ν) :
    ∀ᵐ ω ∂μ, ∀ n, mcEstimate f X n ω = mcEstimate g X n ω := by
  have h : ∀ᵐ ω ∂μ, ∀ i, f (X i ω) = g (X i ω) := by
    refine ae_all_iff.2 fun i ↦ ?_
    have h := hfg
    rw [← hlaw i] at h
    exact ae_of_ae_map (hX i).aemeasurable h
  filter_upwards [h] with ω h n
  simp only [mcEstimate, h]

private theorem integral_mcEstimate_aux {ν : Measure α} {f : α → ℝ} (hfi : Integrable f ν)
    {X : ℕ → Ω → α} (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, μ.map (X i) = ν) {n : ℕ}
    (hn : n ≠ 0) : ∫ ω, mcEstimate f X n ω ∂μ = ∫ x, f x ∂ν := by
  have hg : Measurable (hfi.aestronglyMeasurable.mk f) :=
    hfi.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfg := hfi.aestronglyMeasurable.ae_eq_mk
  have he : (fun ω ↦ mcEstimate f X n ω) =ᵐ[μ]
      fun ω ↦ mcEstimate (hfi.aestronglyMeasurable.mk f) X n ω :=
    (mcEstimate_ae_eq_aux hfg hX hlaw).mono fun ω h ↦ h n
  rw [integral_congr_ae he, integral_mcEstimate hg (hfi.congr hfg) hX hlaw hn,
    integral_congr_ae hfg]

private theorem tendsto_mcEstimate_aux {ν : Measure α} {f : α → ℝ} (hfi : Integrable f ν)
    {X : ℕ → Ω → α} (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, μ.map (X i) = ν)
    (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ mcEstimate f X n ω) atTop (𝓝 (∫ x, f x ∂ν)) := by
  have hg : Measurable (hfi.aestronglyMeasurable.mk f) :=
    hfi.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfg := hfi.aestronglyMeasurable.ae_eq_mk
  filter_upwards [mcEstimate_ae_eq_aux hfg hX hlaw,
    tendsto_mcEstimate hg (hfi.congr hfg) hX hlaw hindep] with ω h1 h2
  rw [integral_congr_ae hfg]
  simpa only [h1] using h2

/-- **Importance sampling is unbiased** for an integrand that is only integrable under the
target `ρ.withDensity w`. -/
theorem integral_isEstimate_of_integrable {ρ : Measure α} {w : α → ℝ≥0∞}
    (hw : Measurable w) (hwt : ∀ᵐ x ∂ρ, w x < ∞) {f : α → ℝ}
    (hfi : Integrable f (ρ.withDensity w)) {X : ℕ → Ω → α} (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = ρ) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, isEstimate w f X n ω ∂μ = ∫ x, f x ∂(ρ.withDensity w) := by
  rw [← integral_weight_mul hw hwt]
  exact integral_mcEstimate_aux ((integrable_withDensity_iff_integrable_smul' hw hwt).mp hfi) hX hlaw hn

/-- **Importance sampling is consistent** for an integrand that is only integrable under the
target `ρ.withDensity w`, with pairwise independent samples from `ρ`. -/
theorem tendsto_isEstimate_of_integrable {ρ : Measure α} {w : α → ℝ≥0∞}
    (hw : Measurable w) (hwt : ∀ᵐ x ∂ρ, w x < ∞) {f : α → ℝ}
    (hfi : Integrable f (ρ.withDensity w)) {X : ℕ → Ω → α} (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = ρ) (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ isEstimate w f X n ω) atTop
      (𝓝 (∫ x, f x ∂(ρ.withDensity w))) := by
  rw [← integral_weight_mul hw hwt]
  exact tendsto_mcEstimate_aux ((integrable_withDensity_iff_integrable_smul' hw hwt).mp hfi) hX hlaw
    hindep

/-- **Importance sampling is unbiased** for a target `ν ≪ ρ` with the Radon–Nikodym weight
`ν.rnDeriv ρ`. -/
theorem integral_isEstimate_rnDeriv {ν ρ : Measure α} [SigmaFinite ν] [SigmaFinite ρ]
    (hνρ : ν ≪ ρ) {f : α → ℝ} (hfi : Integrable f ν) {X : ℕ → Ω → α}
    (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, μ.map (X i) = ρ) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, isEstimate (ν.rnDeriv ρ) f X n ω ∂μ = ∫ x, f x ∂ν := by
  have h := integral_isEstimate_of_integrable (Measure.measurable_rnDeriv ν ρ)
    (Measure.rnDeriv_lt_top ν ρ) (by rwa [Measure.withDensity_rnDeriv_eq ν ρ hνρ]) hX hlaw hn
  rwa [Measure.withDensity_rnDeriv_eq ν ρ hνρ] at h

/-- **Importance sampling is consistent** for a target `ν ≪ ρ` with the Radon–Nikodym weight
`ν.rnDeriv ρ` and pairwise independent samples from `ρ`. -/
theorem tendsto_isEstimate_rnDeriv {ν ρ : Measure α} [SigmaFinite ν] [SigmaFinite ρ]
    (hνρ : ν ≪ ρ) {f : α → ℝ} (hfi : Integrable f ν) {X : ℕ → Ω → α}
    (hX : ∀ i, Measurable (X i)) (hlaw : ∀ i, μ.map (X i) = ρ)
    (hindep : Pairwise fun i j ↦ IndepFun (X i) (X j) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ isEstimate (ν.rnDeriv ρ) f X n ω) atTop (𝓝 (∫ x, f x ∂ν)) := by
  have h := tendsto_isEstimate_of_integrable (Measure.measurable_rnDeriv ν ρ)
    (Measure.rnDeriv_lt_top ν ρ) (by rwa [Measure.withDensity_rnDeriv_eq ν ρ hνρ]) hX hlaw hindep
  rwa [Measure.withDensity_rnDeriv_eq ν ρ hνρ] at h

/-- With the weight `1` (target = proposal), importance sampling is plain Monte Carlo. -/
theorem isEstimate_one (f : α → ℝ) (X : ℕ → Ω → α) (n : ℕ) (ω : Ω) :
    isEstimate 1 f X n ω = mcEstimate f X n ω := by
  simp [isEstimate]

end Cslib.MachineLearning.Sampling
