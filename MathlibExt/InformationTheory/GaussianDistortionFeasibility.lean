/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ConditionalEntropy
public import MathlibExt.InformationTheory.MutualInformationDPI
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Gaussian distortion feasibility

For a joint law on source/reproduction pairs, distortion
feasibility at a level `D ≥ 0` for a Gaussian source of variance
`sigma^2` is exactly: the source marginal is `N(0, sigma^2)`, the
square error is integrable, and the expected square error is at
most `D`. Negative levels are never feasible. The mutual-information characterization uses the
canonical `measureMutualInformation` from the information-theory
library.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MathlibExt.InformationTheory.GaussianDistortionFeasibility

open _root_.InformationTheory

/-! ### Private helpers (not part of the pin) -/

private theorem measurable_sq_error_fun :
    Measurable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) :=
  ((continuous_fst.sub continuous_snd).pow 2).measurable

private theorem aestrongly_sq_error_fun (μ : Measure (ℝ × ℝ)) :
    AEStronglyMeasurable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) μ :=
  measurable_sq_error_fun.aestronglyMeasurable

private theorem measurable_sq_error_ennreal :
    Measurable (fun z : ℝ × ℝ => ENNReal.ofReal ((z.1 - z.2) ^ 2)) :=
  measurable_sq_error_fun.ennreal_ofReal

private theorem measurable_heavyTail_fun :
    Measurable (fun x : ℝ => (x, x - Real.exp (x ^ 2 / 4))) := by
  have hpow : Measurable (fun x : ℝ => x ^ 2 / 4) :=
    (measurable_id.pow_const 2).div_const 4
  have hexp : Measurable (fun x : ℝ => Real.exp (x ^ 2 / 4)) :=
    Real.continuous_exp.measurable.comp hpow
  exact measurable_id.prodMk (measurable_id.sub hexp)

/-! ### Definitions -/

/-- Joint laws of `(X, X̂)` with source marginal `N(0, σ2)` and square-error distortion at most
`D`, measured by the lower integral `∫⁻ ofReal ((x - x̂)²) ≤ ofReal D`. The level must satisfy
`0 ≤ D`: a negative level is infeasible rather than truncated to `0` by `ENNReal.ofReal`. -/
def distortionFeasible (σ2 : ℝ≥0) (D : ℝ) : Set (ProbabilityMeasure (ℝ × ℝ)) :=
  {μ | 0 ≤ D ∧ (μ : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 σ2 ∧
    ∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2) ∂(μ : Measure (ℝ × ℝ)) ≤ ENNReal.ofReal D}

/-- Gaussian rate-distortion function `R(D)` in bits: the `ℝ≥0∞` infimum of the mutual
information over the distortion-feasible joint laws (so `R(D) = ⊤` for `D < 0`). -/
noncomputable def rateDistortion (σ2 : ℝ≥0) (D : ℝ) : ℝ≥0∞ :=
  ⨅ μ ∈ distortionFeasible σ2 D, measureMutualInformation μ

/-! ### Lower-integral versus Bochner-integral feasibility -/

/-- For a probability law on `ℝ × ℝ`, the square error is integrable iff its lower integral is
finite. -/
theorem integrable_sq_error_iff_lintegral_lt_top (μ : ProbabilityMeasure (ℝ × ℝ)) :
    Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) (μ : Measure (ℝ × ℝ)) ↔
      ∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2) ∂(μ : Measure (ℝ × ℝ)) < ∞ := by
  have hmeas : AEStronglyMeasurable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2)
      (μ : Measure (ℝ × ℝ)) :=
    aestrongly_sq_error_fun _
  have hnn : ∀ z : ℝ × ℝ, ENNReal.ofReal ((z.1 - z.2) ^ 2) =
      (‖(z.1 - z.2) ^ 2‖₊ : ℝ≥0∞) := by
    intro z
    rw [ENNReal.ofReal_eq_coe_nnreal (sq_nonneg _),
      Real.nnnorm_of_nonneg (sq_nonneg _)]
  have heq : (∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2) ∂(μ : Measure (ℝ × ℝ))) =
      ∫⁻ z, (‖(z.1 - z.2) ^ 2‖₊ : ℝ≥0∞) ∂(μ : Measure (ℝ × ℝ)) :=
    lintegral_congr hnn
  rw [heq]
  constructor
  · intro h
    exact h.hasFiniteIntegral
  · intro h
    exact ⟨hmeas, h⟩

/-- For an integrable square error, the real expectation and the lower integral agree through
`ENNReal.ofReal`. -/
theorem ofReal_integral_sq_error_eq_lintegral (μ : ProbabilityMeasure (ℝ × ℝ))
    (hint : Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) (μ : Measure (ℝ × ℝ))) :
    ENNReal.ofReal (∫ z, (z.1 - z.2) ^ 2 ∂(μ : Measure (ℝ × ℝ))) =
      ∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2) ∂(μ : Measure (ℝ × ℝ)) := by
  exact ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun z => sq_nonneg _)

/-- **Finite-distortion equivalence.** For any variance `σ2` and finite `D ≥ 0`, a joint law is
distortion-feasible iff it has source marginal `N(0, σ2)`, an integrable square error, and real
expected square error at most `D`. -/
theorem mem_distortionFeasible_iff {σ2 : ℝ≥0} {D : ℝ} (hD : 0 ≤ D)
    (μ : ProbabilityMeasure (ℝ × ℝ)) :
    μ ∈ distortionFeasible σ2 D ↔
      (μ : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 σ2 ∧
        Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) (μ : Measure (ℝ × ℝ)) ∧
        ∫ z, (z.1 - z.2) ^ 2 ∂(μ : Measure (ℝ × ℝ)) ≤ D := by
  constructor
  · rintro ⟨-, hmap, hle⟩
    have hlt : (∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2)
        ∂(μ : Measure (ℝ × ℝ))) < ∞ :=
      lt_of_le_of_lt hle ENNReal.ofReal_lt_top
    have hint : Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2)
        (μ : Measure (ℝ × ℝ)) :=
      (integrable_sq_error_iff_lintegral_lt_top μ).mpr hlt
    have heq := ofReal_integral_sq_error_eq_lintegral μ hint
    have hle2 : ENNReal.ofReal (∫ z, (z.1 - z.2) ^ 2 ∂(μ : Measure (ℝ × ℝ))) ≤
        ENNReal.ofReal D := by
      rw [heq]
      exact hle
    have hleD : (∫ z, (z.1 - z.2) ^ 2 ∂(μ : Measure (ℝ × ℝ))) ≤ D :=
      (ENNReal.ofReal_le_ofReal_iff hD).mp hle2
    exact ⟨hmap, hint, hleD⟩
  · rintro ⟨hmap, hint, hleD⟩
    have heq := ofReal_integral_sq_error_eq_lintegral μ hint
    have hle2 : ENNReal.ofReal (∫ z, (z.1 - z.2) ^ 2 ∂(μ : Measure (ℝ × ℝ))) ≤
        ENNReal.ofReal D :=
      ENNReal.ofReal_le_ofReal hleD
    have hle : (∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2)
        ∂(μ : Measure (ℝ × ℝ))) ≤ ENNReal.ofReal D := by
      rw [← heq]
      exact hle2
    exact ⟨hD, hmap, hle⟩

/-! ### Headline -/

/-- **Gaussian rate-distortion as a shared variational target.** For the source `N(0, σ2)` and
finite `D ≥ 0`, the lower-integral feasibility defining `R(D)` is equivalent to an
integrable square error with real expectation at most `D`, so `R(D)` is the `ℝ≥0∞` infimum of the
mutual information over joint laws with that marginal, integrable square error and
`E[(X - X̂)²] ≤ D`. -/
theorem rateDistortion_eq_iInf_integrable {σ2 : ℝ≥0} {D : ℝ} (hD : 0 ≤ D) :
    (∀ μ : ProbabilityMeasure (ℝ × ℝ), μ ∈ distortionFeasible σ2 D ↔
      (μ : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 σ2 ∧
        Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) (μ : Measure (ℝ × ℝ)) ∧
        ∫ z, (z.1 - z.2) ^ 2 ∂(μ : Measure (ℝ × ℝ)) ≤ D) ∧
      rateDistortion σ2 D =
        ⨅ μ ∈ {μ : ProbabilityMeasure (ℝ × ℝ) |
          (μ : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 σ2 ∧
            Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) (μ : Measure (ℝ × ℝ)) ∧
            ∫ z, (z.1 - z.2) ^ 2 ∂(μ : Measure (ℝ × ℝ)) ≤ D},
          measureMutualInformation μ := by
  have hmem : ∀ μ : ProbabilityMeasure (ℝ × ℝ), μ ∈ distortionFeasible σ2 D ↔
      (μ : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 σ2 ∧
        Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) (μ : Measure (ℝ × ℝ)) ∧
        ∫ z, (z.1 - z.2) ^ 2 ∂(μ : Measure (ℝ × ℝ)) ≤ D :=
    fun μ => mem_distortionFeasible_iff hD μ
  have hset : distortionFeasible σ2 D =
      {μ : ProbabilityMeasure (ℝ × ℝ) |
        (μ : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 σ2 ∧
          Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2) (μ : Measure (ℝ × ℝ)) ∧
          ∫ z, (z.1 - z.2) ^ 2 ∂(μ : Measure (ℝ × ℝ)) ≤ D} :=
    Set.ext fun μ => hmem μ
  refine ⟨hmem, ?_⟩
  unfold rateDistortion
  rw [hset]

/-! ### Reconstruction kernels by standard-Borel disintegration -/

/-- A joint law with source marginal `N(0, σ2)` is the source composed with its conditional
reconstruction kernel (standard-Borel disintegration). -/
theorem eq_compProd_condKernel_of_map_fst_eq {σ2 : ℝ≥0} (μ : ProbabilityMeasure (ℝ × ℝ))
    (hμ : (μ : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 σ2) :
    (μ : Measure (ℝ × ℝ)) = gaussianReal 0 σ2 ⊗ₘ (μ : Measure (ℝ × ℝ)).condKernel := by
  have h := (μ : Measure (ℝ × ℝ)).disintegrate (μ : Measure (ℝ × ℝ)).condKernel
  rw [Measure.fst, hμ] at h
  exact h.symm

/-- For `D ≥ 0`, a reconstruction kernel `κ` gives a feasible joint law `N(0, σ2) ⊗ₘ κ` iff its
iterated lower-integral distortion is at most `ofReal D`. -/
theorem compProd_mem_distortionFeasible_iff (σ2 : ℝ≥0) {D : ℝ} (hD : 0 ≤ D) (κ : Kernel ℝ ℝ)
    [IsMarkovKernel κ] :
    (⟨gaussianReal 0 σ2 ⊗ₘ κ, inferInstance⟩ : ProbabilityMeasure (ℝ × ℝ)) ∈
        distortionFeasible σ2 D ↔
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((x - y) ^ 2) ∂(κ x) ∂(gaussianReal 0 σ2) ≤
        ENNReal.ofReal D := by
  have hmap : (gaussianReal 0 σ2 ⊗ₘ κ).map Prod.fst = gaussianReal 0 σ2 :=
    Measure.fst_compProd _ _
  have hlin : (∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2) ∂(gaussianReal 0 σ2 ⊗ₘ κ)) =
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((x - y) ^ 2) ∂(κ x) ∂(gaussianReal 0 σ2) :=
    Measure.lintegral_compProd measurable_sq_error_ennreal
  change (0 ≤ D ∧ (gaussianReal 0 σ2 ⊗ₘ κ).map Prod.fst = gaussianReal 0 σ2 ∧
    ∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2) ∂(gaussianReal 0 σ2 ⊗ₘ κ) ≤ ENNReal.ofReal D) ↔ _
  rw [hmap, hlin]
  simp [hD]

/-! ### Validation: independent constant reconstruction at `D = σ2` -/

/-- Independent constant reconstruction `X̂ = 0`: the law `N(0, σ2) ⊗ δ₀`. -/
noncomputable def constantReconstruction (σ2 : ℝ≥0) : ProbabilityMeasure (ℝ × ℝ) :=
  ⟨(gaussianReal 0 σ2).prod (Measure.dirac 0), inferInstance⟩

/-- Constant reconstruction is feasible at `D = σ2`: `∫⁻ ofReal (x²) dN(0, σ2) = ofReal σ2`. -/
theorem constantReconstruction_mem_distortionFeasible (σ2 : ℝ≥0) :
    constantReconstruction σ2 ∈ distortionFeasible σ2 σ2 := by
  have hmap : ((gaussianReal 0 σ2).prod (Measure.dirac (0 : ℝ))).map Prod.fst =
      gaussianReal 0 σ2 := by
    simp
  have hprod : (∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2)
      ∂((gaussianReal 0 σ2).prod (Measure.dirac (0 : ℝ)))) =
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((x - y) ^ 2) ∂(Measure.dirac (0 : ℝ))
        ∂(gaussianReal 0 σ2) :=
    lintegral_prod _ measurable_sq_error_ennreal.aemeasurable
  have hdirac : ∀ x : ℝ, (∫⁻ y, ENNReal.ofReal ((x - y) ^ 2) ∂(Measure.dirac (0 : ℝ))) =
      ENNReal.ofReal (x ^ 2) := by
    intro x
    rw [lintegral_dirac]
    simp
  have hinner : (∫⁻ x, ∫⁻ y, ENNReal.ofReal ((x - y) ^ 2) ∂(Measure.dirac (0 : ℝ))
      ∂(gaussianReal 0 σ2)) =
      ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(gaussianReal 0 σ2) :=
    lintegral_congr hdirac
  have hmem : MemLp id 2 (gaussianReal 0 σ2) := memLp_id_gaussianReal 2
  have hvar : variance id (gaussianReal 0 σ2) = (σ2 : ℝ) := variance_id_gaussianReal
  have hsub : variance id (gaussianReal 0 σ2) =
      (∫ x, (id x) ^ 2 ∂(gaussianReal 0 σ2)) -
        (∫ x, id x ∂(gaussianReal 0 σ2)) ^ 2 :=
    variance_eq_sub hmem
  have hint1 : (∫ x, id x ∂(gaussianReal 0 σ2)) = 0 := integral_id_gaussianReal
  have hint2 : Integrable (fun x : ℝ => (id x) ^ 2) (gaussianReal 0 σ2) :=
    hmem.integrable_sq
  have heq : (∫ x, (id x) ^ 2 ∂(gaussianReal 0 σ2)) -
      (∫ x, id x ∂(gaussianReal 0 σ2)) ^ 2 = (σ2 : ℝ) :=
    hsub.symm.trans hvar
  rw [hint1] at heq
  simp at heq
  have hsq0 : (∫ x, x ^ 2 ∂(gaussianReal 0 σ2)) = (σ2 : ℝ) := heq
  have hintSq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 σ2) := hint2
  have hlin_eq : ENNReal.ofReal (∫ x, x ^ 2 ∂(gaussianReal 0 σ2)) =
      ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(gaussianReal 0 σ2) :=
    ofReal_integral_eq_lintegral_ofReal hintSq (Filter.Eventually.of_forall fun x => sq_nonneg _)
  rw [hsq0] at hlin_eq
  have hfinal : (∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2)
      ∂((gaussianReal 0 σ2).prod (Measure.dirac (0 : ℝ)))) = ENNReal.ofReal σ2 := by
    rw [hprod, hinner, ← hlin_eq]
  exact ⟨NNReal.coe_nonneg σ2, hmap, hfinal.le⟩

/-- Constant reconstruction carries zero mutual information. -/
theorem measureMutualInformation_constantReconstruction (σ2 : ℝ≥0) :
    measureMutualInformation (constantReconstruction σ2) = 0 := by
  unfold measureMutualInformation
  have hfst : ((constantReconstruction σ2 : Measure (ℝ × ℝ)).map Prod.fst) =
      gaussianReal 0 σ2 := by
    show ((gaussianReal 0 σ2).prod (Measure.dirac (0 : ℝ))).map Prod.fst = _
    rw [Measure.map_fst_prod]
    simp
  have hsnd : ((constantReconstruction σ2 : Measure (ℝ × ℝ)).map Prod.snd) =
      Measure.dirac 0 := by
    show ((gaussianReal 0 σ2).prod (Measure.dirac (0 : ℝ))).map Prod.snd = _
    rw [Measure.map_snd_prod]
    simp
  rw [hfst, hsnd]
  show klDiv ((gaussianReal 0 σ2).prod (Measure.dirac (0 : ℝ)))
    ((gaussianReal 0 σ2).prod (Measure.dirac (0 : ℝ))) / _ = 0
  rw [klDiv_self, ENNReal.zero_div]

/-- Hence `R(σ2) = 0`. -/
theorem rateDistortion_self_eq_zero (σ2 : ℝ≥0) :
    rateDistortion σ2 σ2 = 0 := by
  have hmem := constantReconstruction_mem_distortionFeasible σ2
  have hMI := measureMutualInformation_constantReconstruction σ2
  have hle : rateDistortion σ2 σ2 ≤
      measureMutualInformation (constantReconstruction σ2) :=
    iInf_le_of_le (constantReconstruction σ2) (iInf_le_of_le hmem le_rfl)
  rw [hMI] at hle
  exact le_antisymm hle bot_le

/-! ### Validation: an infinite lower integral is never admissible -/

/-- Heavy-tailed reconstruction for the standard source: `X̂ = X - exp (X² / 4)`, so
`(X - X̂)² = exp (X² / 2)`, whose `N(0, 1)` lower integral is infinite. -/
noncomputable def heavyTailReconstruction : ProbabilityMeasure (ℝ × ℝ) :=
  ⟨(gaussianReal 0 1).map (fun x => (x, x - Real.exp (x ^ 2 / 4))), inferInstance⟩

/-- Its source marginal is `N(0, 1)`. -/
theorem heavyTailReconstruction_map_fst :
    (heavyTailReconstruction : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 1 := by
  have hmeas : Measurable (fun x : ℝ => (x, x - Real.exp (x ^ 2 / 4))) :=
    measurable_heavyTail_fun
  have hcomp : (Prod.fst ∘ fun x : ℝ => (x, x - Real.exp (x ^ 2 / 4))) = id := rfl
  have heq : ((gaussianReal 0 1).map
      (fun x : ℝ => (x, x - Real.exp (x ^ 2 / 4)))).map Prod.fst =
      (gaussianReal 0 1).map
        (Prod.fst ∘ fun x : ℝ => (x, x - Real.exp (x ^ 2 / 4))) :=
    Measure.map_map measurable_fst hmeas
  rw [hcomp, Measure.map_id] at heq
  show ((gaussianReal 0 1).map
    (fun x : ℝ => (x, x - Real.exp (x ^ 2 / 4)))).map Prod.fst = _
  exact heq

/-- Its square-error lower integral is infinite. -/
theorem lintegral_sq_error_heavyTailReconstruction :
    ∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2) ∂(heavyTailReconstruction : Measure (ℝ × ℝ)) = ∞ := by
  have hmeasF : Measurable (fun x : ℝ => (x, x - Real.exp (x ^ 2 / 4))) :=
    measurable_heavyTail_fun
  have hmap : (∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2)
      ∂((gaussianReal 0 1).map (fun x : ℝ => (x, x - Real.exp (x ^ 2 / 4))))) =
      ∫⁻ x, ENNReal.ofReal (Real.exp (x ^ 2 / 2)) ∂(gaussianReal 0 1) := by
    rw [lintegral_map measurable_sq_error_ennreal hmeasF]
    apply lintegral_congr
    intro x
    have hsub : x - (x - Real.exp (x ^ 2 / 4)) = Real.exp (x ^ 2 / 4) := by ring
    have hexp : (Real.exp (x ^ 2 / 4)) ^ 2 = Real.exp (x ^ 2 / 2) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simp [hsub, hexp]
  have hgauss : gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1) := by
    simp [gaussianReal]
  have hwith : (∫⁻ x, ENNReal.ofReal (Real.exp (x ^ 2 / 2)) ∂(gaussianReal 0 1)) =
      ∫⁻ _ : ℝ, ENNReal.ofReal ((√(2 * Real.pi))⁻¹) ∂volume := by
    rw [hgauss, lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) (by fun_prop)]
    apply lintegral_congr
    intro x
    have hexp_nn : 0 ≤ Real.exp (x ^ 2 / 2) := (Real.exp_pos _).le
    have hpdf : gaussianPDF 0 1 x =
        ENNReal.ofReal ((√(2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2))) := by
      simp [gaussianPDF, gaussianPDFReal, neg_div]
    have hpdf_nn : 0 ≤ (√(2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
      positivity
    rw [Pi.mul_apply, hpdf, ← ENNReal.ofReal_mul hpdf_nn]
    congr 1
    have hmul : (√(2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) * Real.exp (x ^ 2 / 2) =
        (√(2 * Real.pi))⁻¹ * (Real.exp (x ^ 2 / 2) * Real.exp (-(x ^ 2 / 2))) := by
      ring
    rw [hmul, ← Real.exp_add]
    simp
  have hvol : (∫⁻ _ : ℝ, ENNReal.ofReal ((√(2 * Real.pi))⁻¹) ∂volume) = ∞ := by
    rw [lintegral_const]
    have hpos : (0 : ℝ) < (√(2 * Real.pi))⁻¹ := by
      apply inv_pos.mpr
      apply Real.sqrt_pos.mpr
      positivity
    have hne : ENNReal.ofReal ((√(2 * Real.pi))⁻¹) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr hpos)
    rw [Real.volume_univ, ENNReal.mul_top hne]
  show (∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2)
    ∂((gaussianReal 0 1).map (fun x : ℝ => (x, x - Real.exp (x ^ 2 / 4))))) = ∞
  rw [hmap, hwith, hvol]

/-- So it is infeasible at every distortion level. -/
theorem heavyTailReconstruction_not_mem_distortionFeasible (D : ℝ) :
    heavyTailReconstruction ∉ distortionFeasible 1 D := by
  intro hmem
  obtain ⟨_, _, hle⟩ := hmem
  rw [lintegral_sq_error_heavyTailReconstruction] at hle
  exact (not_le_of_gt ENNReal.ofReal_lt_top) hle

/-- Yet its unguarded real Bochner integral of the square error is `0`, which would pass the
test `∫ (X - X̂)² ≤ D` for every `D ≥ 0`: the real integral alone is not a feasibility test. -/
theorem integral_sq_error_heavyTailReconstruction :
    ∫ z, (z.1 - z.2) ^ 2 ∂(heavyTailReconstruction : Measure (ℝ × ℝ)) = 0 := by
  have hnot : ¬ Integrable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2)
      (heavyTailReconstruction : Measure (ℝ × ℝ)) := by
    rw [integrable_sq_error_iff_lintegral_lt_top]
    rw [lintegral_sq_error_heavyTailReconstruction]
    exact lt_irrefl _
  exact integral_undef hnot

/-! ### Exact reconstruction -/

/-- Exact reconstruction `X̂ = X`: the diagonal image of `N(0, σ2)`. -/
noncomputable def diagonalReconstruction (σ2 : ℝ≥0) : ProbabilityMeasure (ℝ × ℝ) :=
  ⟨(gaussianReal 0 σ2).map (fun x => (x, x)), inferInstance⟩

end MathlibExt.InformationTheory.GaussianDistortionFeasibility
