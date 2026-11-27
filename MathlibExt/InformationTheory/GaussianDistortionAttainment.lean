/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ConditionalEntropy
public import MathlibExt.InformationTheory.GaussianDistortionFeasibility
public import MathlibExt.InformationTheory.ReferenceOutputKL
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
import MathlibExt.InformationTheory.GaussianRateDistortionValue
import MathlibExt.InformationTheory.ScalarGaussianKernelKL
import MathlibExt.Probability.JointLaw

/-!
# Gaussian rate-distortion: attainment by the backward Gaussian test channel

For a Gaussian source of variance `σ2` and a distortion level `0 < D < σ2`, take independent
`X̂ ~ N(0, σ2 - D)` and `Z ~ N(0, D)` and put `X = X̂ + Z`. Then `X ~ N(0, σ2)`, the expected
square error `E[(X - X̂)²]` equals `D`, and the mutual information of `(X, X̂)` is
`log (σ2 / D) / (2 * log 2)` bits. Since this joint law is distortion feasible, the Gaussian
rate-distortion function satisfies `R(D) ≤ log (σ2 / D) / (2 * log 2)`. Together with
`GaussianDistortionConverse.rateDistortion_ge_ofReal_log_div`, which has the same binders and the
same bound term, this pins `R(D)` by `le_antisymm`.

After swapping coordinates, the law of `(X̂, X)` is the input law `N(0, σ2 - D)` composed with
the additive Gaussian noise kernel `x̂ ↦ N(x̂, D)`, so its divergence from
`N(0, σ2 - D) ⊗ N(0, σ2)` is the scalar Gaussian channel divergence
`ScalarGaussianKernelKL.klDiv_compProd_gaussianNoiseKernel_gaussianReal`, which equals
`log (σ2 / D) / 2` nats here.

Conventions:
* variances and distortion levels are `ℝ≥0` (the variance type of Mathlib `gaussianReal`); the
  rate-distortion function takes the level as a real number `(D : ℝ)`;
* the joint law is ordered `(X, X̂)`: source first, reproduction second, as in
  `distortionFeasible`;
* mutual information is the information-theory library's `measureMutualInformation`, in bits,
  valued in `ℝ≥0∞`.

## Main results

* `pairLaw_apply_prod`: the joint law of a.e.-measurable `X` and `Y` gives `A ×ˢ B` the
  probability `P (X ⁻¹' A ∩ Y ⁻¹' B)`.
* `backwardChannelLaw_mem_distortionFeasible`: the backward channel is feasible at level `D`.
* `measureMutualInformation_backwardChannelLaw`: its mutual information is
  `log (σ2 / D) / (2 * log 2)` bits.
* `rateDistortion_le_ofReal_log_div`: the Gaussian rate-distortion upper bound.
* `backwardChannel_attains`: all of the above for random variables on any probability space.

Validation:
* `D = σ2 / 2` with `σ2 > 0`: the backward channel carries exactly one half bit;
* the endpoint `D = σ2` is the independent constant reconstruction, with no density formula;
* violated premises: at `D = 0` the backward law is the diagonal law, and for `σ2 > 0` its mutual
  information is `⊤`, not the value `0` that the zero-denominator logarithm gives; for `D > σ2`
  the truncated variance `σ2 - D = 0` gives the wrong source marginal, so the law is infeasible.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006,
  Theorem 10.3.2 (rate-distortion function of a Gaussian source under squared-error distortion)
  and its achievability construction by the backward test channel.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MathlibExt.InformationTheory.GaussianDistortionAttainment

open _root_.InformationTheory
open MathlibExt.InformationTheory.GaussianDistortionFeasibility

/-! ### Definitions -/

/-- The joint law of a pair of real random variables `(X, Y)` on a probability space, as a
probability measure on `ℝ × ℝ`. Both coordinates must be almost everywhere measurable, so that the
image measure assigns each event its probability (`pairLaw_apply_prod`). -/
noncomputable def pairLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    ProbabilityMeasure (ℝ × ℝ) :=
  ⟨P.map (fun ω => (X ω, Y ω)), (Measure.isProbabilityMeasure_map_iff (hX.prodMk hY)).2 ‹_›⟩

/-- The backward Gaussian test channel: the law of `(X, X̂)` where `X̂ ~ N(0, σ2 - D)` and
`Z ~ N(0, D)` are independent and `X = X̂ + Z`, realized on the product of the two Gaussian
laws. The variance `σ2 - D` is truncated subtraction in `ℝ≥0`. -/
noncomputable def backwardChannelLaw (σ2 D : ℝ≥0) : ProbabilityMeasure (ℝ × ℝ) :=
  ⟨((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map (fun p => (p.1 + p.2, p.1)),
    inferInstance⟩

/-- **The joint law gives rectangles their probability.** For almost everywhere measurable `X`
and `Y` and measurable sets `A` and `B`, the joint law gives `A ×ˢ B` the probability
`P (X ⁻¹' A ∩ Y ⁻¹' B)` that `X ∈ A` and `Y ∈ B`. -/
theorem pairLaw_apply_prod {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (pairLaw P X Y hX hY : Measure (ℝ × ℝ)) (A ×ˢ B) = P (X ⁻¹' A ∩ Y ⁻¹' B) :=
  MathlibExt.Probability.map_prodMk_apply_prod hX hY hA hB

/-! ### Private helpers -/

private theorem measurable_backwardMap :
    Measurable (fun p : ℝ × ℝ => (p.1 + p.2, p.1)) := by
  fun_prop

private theorem measurable_sq_error_ennreal' :
    Measurable (fun z : ℝ × ℝ => ENNReal.ofReal ((z.1 - z.2) ^ 2)) :=
  ((continuous_fst.sub continuous_snd).pow 2).measurable.ennreal_ofReal

private theorem integrable_sq_gaussianReal (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
  (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq

private theorem integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
  have hmem : MemLp id 2 (gaussianReal 0 v) := memLp_id_gaussianReal 2
  have h := variance_eq_sub hmem
  have h1 : (∫ x, id x ∂(gaussianReal 0 v)) = 0 := integral_id_gaussianReal
  rw [variance_id_gaussianReal, h1] at h
  simp at h
  linarith

private theorem lintegral_sq_gaussianReal (v : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(gaussianReal 0 v) = ENNReal.ofReal (v : ℝ) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_sq_gaussianReal v)
    (Filter.Eventually.of_forall fun x => sq_nonneg x), integral_sq_gaussianReal]

/-- The two Gaussian components of the backward channel, as a product measure. -/
private theorem prod_map_snd (σ2 D : ℝ≥0) :
    ((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map Prod.snd = gaussianReal 0 D := by
  rw [Measure.map_snd_prod]
  simp

private theorem prod_map_fst (σ2 D : ℝ≥0) :
    ((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map Prod.fst =
      gaussianReal 0 (σ2 - D) := by
  rw [Measure.map_fst_prod]
  simp

private theorem prod_map_add (σ2 D : ℝ≥0) :
    ((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map (fun p => p.1 + p.2) =
      gaussianReal 0 (σ2 - D + D) := by
  have h : ((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map (fun p => p.1 + p.2) =
      (gaussianReal 0 (σ2 - D)) ∗ (gaussianReal 0 D) := rfl
  rw [h, gaussianReal_conv_gaussianReal, add_zero]

private theorem backwardChannelLaw_coe (σ2 D : ℝ≥0) :
    (backwardChannelLaw σ2 D : Measure (ℝ × ℝ)) =
      ((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map (fun p => (p.1 + p.2, p.1)) :=
  rfl

private theorem backwardChannelLaw_map_fst' (σ2 D : ℝ≥0) :
    (backwardChannelLaw σ2 D : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 (σ2 - D + D) := by
  rw [backwardChannelLaw_coe, Measure.map_map measurable_fst measurable_backwardMap]
  exact prod_map_add σ2 D

private theorem backwardChannelLaw_map_snd (σ2 D : ℝ≥0) :
    (backwardChannelLaw σ2 D : Measure (ℝ × ℝ)).map Prod.snd = gaussianReal 0 (σ2 - D) := by
  rw [backwardChannelLaw_coe, Measure.map_map measurable_snd measurable_backwardMap]
  exact prod_map_fst σ2 D

/-- The core computation: the swapped backward law `(X̂, X)` is the input law `N(0, σ2 - D)`
composed with the noise kernel `x̂ ↦ N(x̂, D)`, and its divergence from
`N(0, σ2 - D) ⊗ N(0, σ2)` is the scalar Gaussian channel divergence. -/
private theorem klDiv_shear (σ2 D : ℝ≥0) (hσ : σ2 ≠ 0) (hD : D ≠ 0) (hDσ2 : D ≤ σ2) :
    klDiv (((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map (fun p => (p.1, p.1 + p.2)))
      ((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 σ2)) =
      ENNReal.ofReal (Real.log ((σ2 : ℝ) / (D : ℝ)) / 2) := by
  have hshear : ((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map
      (fun p => (p.1, p.1 + p.2)) =
      gaussianReal 0 (σ2 - D) ⊗ₘ MetaMathlibExt.noiseKernel id measurable_id (gaussianReal 0 D) :=
    (VectorGaussianKernelKL.compProd_noiseKernel_eq_map id measurable_id _ _).symm
  rw [hshear, ScalarGaussianKernelKL.klDiv_compProd_gaussianNoiseKernel_gaussianReal 0 0 D σ2
    (σ2 - D) (pos_iff_ne_zero.mpr hD) (pos_iff_ne_zero.mpr hσ), NNReal.coe_sub hDσ2]
  congr 1
  have hσ' : (σ2 : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hσ
  have hsum : (D : ℝ) + ((σ2 : ℝ) - (D : ℝ) + (0 - 0) ^ 2) = σ2 := by ring
  rw [hsum, div_self hσ']
  ring

/-! ### Source marginal and distortion -/

/-- For `D ≤ σ2`, the source `X = X̂ + Z` of the backward channel is `N(0, σ2)`. -/
theorem backwardChannelLaw_map_fst (σ2 D : ℝ≥0) (hDσ2 : (D : ℝ) ≤ (σ2 : ℝ)) :
    (backwardChannelLaw σ2 D : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 σ2 := by
  rw [backwardChannelLaw_map_fst', tsub_add_cancel_of_le (by exact_mod_cast hDσ2)]

/-- The square-error lower integral of the backward channel is exactly `ofReal D`. -/
theorem lintegral_sq_error_backwardChannelLaw (σ2 D : ℝ≥0) :
    ∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2) ∂(backwardChannelLaw σ2 D : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (D : ℝ) := by
  rw [backwardChannelLaw_coe, lintegral_map measurable_sq_error_ennreal' measurable_backwardMap]
  simp only [add_sub_cancel_left]
  have h : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (p.2 ^ 2)
      ∂((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D))) =
      ∫⁻ x, ENNReal.ofReal (x ^ 2)
        ∂(((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map Prod.snd) :=
    (lintegral_map (measurable_id.pow_const 2).ennreal_ofReal measurable_snd).symm
  rw [h, prod_map_snd, lintegral_sq_gaussianReal]

/-- The expected square error of the backward channel is exactly `D`. -/
theorem integral_sq_error_backwardChannelLaw (σ2 D : ℝ≥0) :
    ∫ z, (z.1 - z.2) ^ 2 ∂(backwardChannelLaw σ2 D : Measure (ℝ × ℝ)) = (D : ℝ) := by
  rw [backwardChannelLaw_coe, integral_map measurable_backwardMap.aemeasurable (by fun_prop)]
  simp only [add_sub_cancel_left]
  have h : (∫ p : ℝ × ℝ, p.2 ^ 2 ∂((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D))) =
      ∫ x, x ^ 2 ∂(((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map Prod.snd) :=
    (integral_map measurable_snd.aemeasurable (continuous_pow 2).aestronglyMeasurable).symm
  rw [h, prod_map_snd, integral_sq_gaussianReal]

/-- For `D ≤ σ2`, the backward channel is distortion feasible at level `D`. -/
theorem backwardChannelLaw_mem_distortionFeasible (σ2 D : ℝ≥0)
    (hDσ2 : (D : ℝ) ≤ (σ2 : ℝ)) :
    backwardChannelLaw σ2 D ∈ distortionFeasible σ2 (D : ℝ) := by
  exact ⟨D.coe_nonneg, backwardChannelLaw_map_fst σ2 D hDσ2,
    (lintegral_sq_error_backwardChannelLaw σ2 D).le⟩

/-! ### Mutual information and the rate-distortion upper bound -/

/-- For `0 < D < σ2`, the mutual information of `(X, X̂)` under the backward channel is
`log (σ2 / D) / (2 * log 2)` bits. -/
theorem measureMutualInformation_backwardChannelLaw (σ2 D : ℝ≥0)
    (hD : (0 : ℝ) < (D : ℝ)) (hDσ2 : (D : ℝ) < (σ2 : ℝ)) :
    measureMutualInformation (backwardChannelLaw σ2 D) =
      ENNReal.ofReal (Real.log ((σ2 : ℝ) / (D : ℝ)) / (2 * Real.log 2)) := by
  have hD0 : D ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hD
    exact lt_irrefl 0 hD
  have hσ0 : σ2 ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hDσ2
    exact absurd hDσ2 (not_lt.mpr D.coe_nonneg)
  have hle : D ≤ σ2 := by exact_mod_cast hDσ2.le
  unfold measureMutualInformation
  rw [backwardChannelLaw_map_fst σ2 D hDσ2.le, backwardChannelLaw_map_snd]
  have hswap := ReferenceOutputKL.klDiv_map_swap (backwardChannelLaw σ2 D : Measure (ℝ × ℝ))
    ((gaussianReal 0 σ2).prod (gaussianReal 0 (σ2 - D)))
  rw [Measure.prod_swap, backwardChannelLaw_coe,
    Measure.map_map measurable_swap measurable_backwardMap] at hswap
  have hcomp : (Prod.swap ∘ fun p : ℝ × ℝ => (p.1 + p.2, p.1)) = fun p => (p.1, p.1 + p.2) := rfl
  rw [hcomp, klDiv_shear σ2 D hσ0 hD0 hle] at hswap
  rw [backwardChannelLaw_coe, ← hswap,
    ← ENNReal.ofReal_div_of_pos (Real.log_pos one_lt_two)]
  congr 1
  ring

/-- **Gaussian rate-distortion upper bound.** For `0 < D < σ2`, the Gaussian rate-distortion
function at `D`, in bits, is at most `log (σ2 / D) / (2 * log 2)`. -/
theorem rateDistortion_le_ofReal_log_div (σ2 D : ℝ≥0)
    (hD : (0 : ℝ) < (D : ℝ)) (hDσ2 : (D : ℝ) < (σ2 : ℝ)) :
    rateDistortion σ2 (D : ℝ) ≤
      ENNReal.ofReal (Real.log ((σ2 : ℝ) / (D : ℝ)) / (2 * Real.log 2)) := by
  have hmem := backwardChannelLaw_mem_distortionFeasible σ2 D hDσ2.le
  calc rateDistortion σ2 (D : ℝ) ≤ measureMutualInformation (backwardChannelLaw σ2 D) :=
        iInf₂_le _ hmem
    _ = _ := measureMutualInformation_backwardChannelLaw σ2 D hD hDσ2

/-- **Attainment by the backward Gaussian test channel.** Let `0 < D < σ2`, let `X̂` and `Z` be
independent real random variables with `X̂ ~ N(0, σ2 - D)` and `Z ~ N(0, D)`, and let
`X = X̂ + Z`. Then the joint law of `(X, X̂)` (both a.e. measurable, since `X̂` and `Z` are) has
source marginal `N(0, σ2)`, square-error distortion exactly `D` (as a lower integral), is
distortion feasible at `D`, and has mutual information `log (σ2 / D) / (2 * log 2)` bits; hence
`R(D)` is at most that value. -/
theorem backwardChannel_attains (σ2 D : ℝ≥0)
    (hD : (0 : ℝ) < (D : ℝ)) (hDσ2 : (D : ℝ) < (σ2 : ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Xhat Z : Ω → ℝ) (hXhat : HasLaw Xhat (gaussianReal 0 (σ2 - D)) P)
    (hZ : HasLaw Z (gaussianReal 0 D) P) (hindep : IndepFun Xhat Z P)
    (hX : ∀ ω, X ω = Xhat ω + Z ω) :
    let μ := pairLaw P X Xhat ((hXhat.aemeasurable.add hZ.aemeasurable).congr
      (Filter.Eventually.of_forall fun ω => (hX ω).symm)) hXhat.aemeasurable
    (μ : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 σ2 ∧
      ∫⁻ z, ENNReal.ofReal ((z.1 - z.2) ^ 2) ∂(μ : Measure (ℝ × ℝ)) = ENNReal.ofReal (D : ℝ) ∧
      μ ∈ distortionFeasible σ2 (D : ℝ) ∧
      measureMutualInformation μ =
        ENNReal.ofReal (Real.log ((σ2 : ℝ) / (D : ℝ)) / (2 * Real.log 2)) ∧
      rateDistortion σ2 (D : ℝ) ≤
        ENNReal.ofReal (Real.log ((σ2 : ℝ) / (D : ℝ)) / (2 * Real.log 2)) := by
  intro μ
  have hlaw : μ = backwardChannelLaw σ2 D := by
    apply Subtype.ext
    change P.map (fun ω => (X ω, Xhat ω)) =
      ((gaussianReal 0 (σ2 - D)).prod (gaussianReal 0 D)).map (fun p => (p.1 + p.2, p.1))
    have hXfun : (fun ω => (X ω, Xhat ω)) =
        (fun p : ℝ × ℝ => (p.1 + p.2, p.1)) ∘ (fun ω => (Xhat ω, Z ω)) := by
      funext ω
      simp [hX ω]
    rw [hXfun, ← AEMeasurable.map_map_of_aemeasurable measurable_backwardMap.aemeasurable
      (hXhat.aemeasurable.prodMk hZ.aemeasurable),
      (indepFun_iff_map_prod_eq_prod_map_map hXhat.aemeasurable hZ.aemeasurable).1 hindep,
      hXhat.map_eq, hZ.map_eq]
  rw [hlaw]
  exact ⟨backwardChannelLaw_map_fst σ2 D hDσ2.le, lintegral_sq_error_backwardChannelLaw σ2 D,
    backwardChannelLaw_mem_distortionFeasible σ2 D hDσ2.le,
    measureMutualInformation_backwardChannelLaw σ2 D hD hDσ2,
    rateDistortion_le_ofReal_log_div σ2 D hD hDσ2⟩

/-! ### Validation: `D = σ2 / 2` -/

/-- For `σ2 > 0`, at `D = σ2 / 2` the backward channel carries exactly one half bit. -/
theorem measureMutualInformation_backwardChannelLaw_half (σ2 : ℝ≥0) (hσ2 : (0 : ℝ) < (σ2 : ℝ)) :
    measureMutualInformation (backwardChannelLaw σ2 (σ2 / 2)) = ENNReal.ofReal (1 / 2) := by
  have hc : ((σ2 / 2 : ℝ≥0) : ℝ) = (σ2 : ℝ) / 2 := by push_cast; ring
  have hD : (0 : ℝ) < ((σ2 / 2 : ℝ≥0) : ℝ) := by rw [hc]; positivity
  have hDσ2 : ((σ2 / 2 : ℝ≥0) : ℝ) < (σ2 : ℝ) := by rw [hc]; linarith
  rw [measureMutualInformation_backwardChannelLaw σ2 (σ2 / 2) hD hDσ2, hc]
  congr 1
  have h2 : (σ2 : ℝ) / ((σ2 : ℝ) / 2) = 2 := by field_simp
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [h2]
  field_simp

/-- Hence, for `σ2 > 0`, `R(σ2 / 2)` is at most one half bit. -/
theorem rateDistortion_half_le (σ2 : ℝ≥0) (hσ2 : (0 : ℝ) < (σ2 : ℝ)) :
    rateDistortion σ2 ((σ2 / 2 : ℝ≥0) : ℝ) ≤ ENNReal.ofReal (1 / 2) := by
  have hc : ((σ2 / 2 : ℝ≥0) : ℝ) = (σ2 : ℝ) / 2 := by push_cast; ring
  have hD : (0 : ℝ) < ((σ2 / 2 : ℝ≥0) : ℝ) := by rw [hc]; positivity
  have hDσ2 : ((σ2 / 2 : ℝ≥0) : ℝ) < (σ2 : ℝ) := by rw [hc]; linarith
  calc rateDistortion σ2 ((σ2 / 2 : ℝ≥0) : ℝ)
      ≤ measureMutualInformation (backwardChannelLaw σ2 (σ2 / 2)) :=
        iInf₂_le _ (backwardChannelLaw_mem_distortionFeasible σ2 (σ2 / 2) hDσ2.le)
    _ = ENNReal.ofReal (1 / 2) := measureMutualInformation_backwardChannelLaw_half σ2 hσ2

/-! ### Validation: the endpoint `D = σ2` is constant reconstruction -/

/-- At `D = σ2` the reproduction variance is `0`: the backward channel is the independent
constant reconstruction `N(0, σ2) ⊗ δ₀`. -/
theorem backwardChannelLaw_self (σ2 : ℝ≥0) :
    backwardChannelLaw σ2 σ2 = constantReconstruction σ2 := by
  apply Subtype.ext
  change ((gaussianReal 0 (σ2 - σ2)).prod (gaussianReal 0 σ2)).map (fun p => (p.1 + p.2, p.1)) =
    (gaussianReal 0 σ2).prod (Measure.dirac 0)
  rw [tsub_self, gaussianReal_zero_var, Measure.dirac_prod,
    Measure.map_map measurable_backwardMap measurable_prodMk_left, Measure.prod_dirac]
  congr 1
  funext z
  simp

/-- The upper bound extends to the endpoint `D = σ2`, where `log (σ2 / σ2) = 0`; the proof goes
through constant reconstruction, not a zero-variance density formula. -/
theorem rateDistortion_self_le_ofReal_log_div (σ2 : ℝ≥0) :
    rateDistortion σ2 (σ2 : ℝ) ≤
      ENNReal.ofReal (Real.log ((σ2 : ℝ) / (σ2 : ℝ)) / (2 * Real.log 2)) := by
  have hmem := backwardChannelLaw_mem_distortionFeasible σ2 σ2 le_rfl
  have hMI : measureMutualInformation (backwardChannelLaw σ2 σ2) = 0 := by
    rw [backwardChannelLaw_self]
    exact measureMutualInformation_constantReconstruction σ2
  calc rateDistortion σ2 (σ2 : ℝ) ≤ measureMutualInformation (backwardChannelLaw σ2 σ2) :=
        iInf₂_le _ hmem
    _ = 0 := hMI
    _ ≤ _ := bot_le

/-! ### Validation: violated premises -/

/-- At `D = 0` the reproduction is the source itself: the backward channel is the diagonal law
`X̂ = X` of `N(0, σ2)`. -/
theorem backwardChannelLaw_zero (σ2 : ℝ≥0) :
    backwardChannelLaw σ2 0 = diagonalReconstruction σ2 := by
  apply Subtype.ext
  change ((gaussianReal 0 (σ2 - 0)).prod (gaussianReal 0 0)).map (fun p => (p.1 + p.2, p.1)) =
    (gaussianReal 0 σ2).map (fun x => (x, x))
  rw [tsub_zero, gaussianReal_zero_var, Measure.prod_dirac,
    Measure.map_map measurable_backwardMap measurable_prodMk_right]
  congr 1
  funext x
  simp

/-- Violated premise `0 < D`: at `D = 0` the backward channel is the diagonal law `X̂ = X`, and
for `σ2 > 0` its mutual information is `⊤`, while the zero-denominator formula
`log (σ2 / 0) / (2 * log 2)` evaluates to `0` under Lean's conventions `x / 0 = 0` and
`log 0 = 0`; it is not a valid rate. -/
theorem measureMutualInformation_backwardChannelLaw_zero (σ2 : ℝ≥0)
    (hσ2 : (0 : ℝ) < (σ2 : ℝ)) :
    measureMutualInformation (backwardChannelLaw σ2 0) = ⊤ ∧
      ENNReal.ofReal (Real.log ((σ2 : ℝ) / ((0 : ℝ≥0) : ℝ)) / (2 * Real.log 2)) = 0 := by
  refine ⟨?_, by simp⟩
  rw [backwardChannelLaw_zero]
  exact GaussianRateDistortionValue.measureMutualInformation_diagonalReconstruction
    (NNReal.coe_pos.mp hσ2)

/-- Violated premise `D < σ2`: for `D > σ2` the truncated reproduction variance is `0`, the
source marginal is `N(0, D)` rather than `N(0, σ2)`, and the backward law is infeasible. -/
theorem backwardChannelLaw_not_mem_distortionFeasible (σ2 D : ℝ≥0)
    (hσ2D : (σ2 : ℝ) < (D : ℝ)) :
    backwardChannelLaw σ2 D ∉ distortionFeasible σ2 (D : ℝ) := by
  rintro ⟨_, hmap, _⟩
  rw [backwardChannelLaw_map_fst'] at hmap
  have hle : σ2 ≤ D := by exact_mod_cast hσ2D.le
  rw [tsub_eq_zero_of_le hle, zero_add] at hmap
  have hDσ : D = σ2 := (gaussianReal_ext_iff.1 hmap).2
  rw [hDσ] at hσ2D
  exact lt_irrefl _ hσ2D

end MathlibExt.InformationTheory.GaussianDistortionAttainment
