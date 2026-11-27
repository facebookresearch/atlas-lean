/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.Distributions.Gaussian.Fernique
import MathlibExt.InformationTheory.DonskerVaradhan
import MathlibExt.Probability.GaussianLogSobolev

/-!
# Talagrand's transport inequality for the Gaussian measure

C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Definition 22.1
and Example 22.15; M. Talagrand, Geom. Funct. Anal. 6 (1996) 587–600.

The main result, `talagrand_stdGaussian`, states that the standard Gaussian measure `γ` on a
finite-dimensional real inner product space satisfies `W₂(μ, γ)² ≤ 2 KL(μ ‖ γ)` for every
probability measure `μ` with finite second moment.

## Proof outline

The proof goes through the dual form of the inequality: it is the implication (2) ⇒ (1) of the
dual characterization of transport inequalities (N. Gozlan and C. Léonard, *Transport
inequalities. A survey*, Markov Process. Related Fields 16 (2010), 635–736, arXiv:1003.3852,
Theorem 3.2, after S. G. Bobkov and F. Götze), with `α(r) = r` and `s = 1`. The dual condition
comes from the Prékopa–Leindler inequality, as in Maurey's proof that the Gaussian measure has
Property `(τ)` (Gozlan and Léonard, Section 8.1), here with a parameter `t ∈ (0, 1)` that tends
to `0` at the end, which gives the sharp constant `2`.

1. *Infimal convolution.* The Prékopa–Leindler inequality for Lebesgue measure
   (`MathlibExt.MeasureTheory.Integral.PrekopaLeindler`), multiplied by the Gaussian density,
   applied to `u = e^{t ψ / (1 - t)}`, `v = e^φ` and `w = 1`, followed by Jensen's inequality for
   `u`, gives `∫ e^φ dγ ≤ e^{-∫ ψ dγ}` whenever `φ(x) + ψ(y) ≤ (1 - t) ‖x - y‖² / 2`.
2. *Compactness.* The radial projection `P_R x = (R / max R ‖x‖) x` onto the closed ball of
   radius `R` is `1`-Lipschitz, so step 1 also holds for the image `γ_R` of `γ` under `P_R`, with
   potentials on the ball. By the data processing inequality, the image `μ_R` of `μ` satisfies
   `KL(μ_R ‖ γ_R) ≤ KL(μ ‖ γ)`.
3. *Duality.* The Donsker–Varadhan inequality (`MathlibExt.InformationTheory.DonskerVaradhan`)
   and step 2 bound every dual value `∫ φ dμ_R + ∫ ψ dγ_R`, for continuous `φ, ψ` with
   `φ(x) + ψ(y) ≤ ‖x - y‖²`, by `2 KL(μ ‖ γ) / (1 - t)`. Kantorovich duality on the compact ball
   (`MathlibExt.MeasureTheory.OptimalTransport.Kantorovich`) turns this into
   `W₂(μ_R, γ_R)² ≤ 2 KL(μ ‖ γ) / (1 - t)`, and `t → 0` gives `W₂(μ_R, γ_R)² ≤ 2 KL(μ ‖ γ)`.
4. *Approximation.* `W₂(μ, μ_R)² ≤ ∫ ‖x - P_R x‖² dμ` tends to `0` as `R → ∞` by dominated
   convergence, since `μ` has finite second moment, and so does `W₂(γ_R, γ)`, since `γ` has finite
   moments (Fernique's theorem). The triangle inequality for `W₂` concludes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

open MathlibExt.Probability.GaussianLogSobolevWanted (lintegral_rpow_mul_le_stdGaussian)
open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (IsCoupling)
open MathlibExt.MeasureTheory.OptimalTransport.Wasserstein (wasserstein transportCost
  wasserstein_le_of_isCoupling wasserstein_triangle)

namespace MathlibExt.Probability.TalagrandTransportWanted

section RadialProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The radial projection `x ↦ (R / max R ‖x‖) • x` onto the closed ball of radius `R`. -/
private noncomputable def radialProj (R : ℝ) (x : E) : E := (R / max R ‖x‖) • x

omit [InnerProductSpace ℝ E] in
private lemma radialProj_coeff_nonneg {R : ℝ} (hR : 0 < R) (x : E) : 0 ≤ R / max R ‖x‖ :=
  div_nonneg hR.le (hR.le.trans (le_max_left _ _))

omit [InnerProductSpace ℝ E] in
private lemma radialProj_coeff_le_one {R : ℝ} (hR : 0 < R) (x : E) : R / max R ‖x‖ ≤ 1 :=
  (div_le_one (hR.trans_le (le_max_left _ _))).2 (le_max_left _ _)

private lemma norm_radialProj_le {R : ℝ} (hR : 0 < R) (x : E) : ‖radialProj R x‖ ≤ R := by
  have hm : 0 < max R ‖x‖ := hR.trans_le (le_max_left _ _)
  rw [radialProj, norm_smul, Real.norm_eq_abs, abs_of_nonneg (radialProj_coeff_nonneg hR x),
    div_mul_eq_mul_div, div_le_iff₀ hm]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hR.le

private lemma radialProj_of_norm_le {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) :
    radialProj R x = x := by
  rw [radialProj, max_eq_left hx, div_self hR.ne', one_smul]

private lemma sub_radialProj {R : ℝ} (x : E) :
    x - radialProj R x = (1 - R / max R ‖x‖) • x := by
  rw [radialProj, sub_smul, one_smul]

private lemma norm_sub_radialProj_le {R : ℝ} (hR : 0 < R) (x : E) :
    ‖x - radialProj R x‖ ≤ ‖x‖ := by
  rw [sub_radialProj, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.2 (radialProj_coeff_le_one hR x))]
  exact mul_le_of_le_one_left (norm_nonneg _) (sub_le_self _ (radialProj_coeff_nonneg hR x))

/-- The variational inequality of the projection onto the ball: `⟪x - P x, z - P x⟫ ≤ 0` for every
`z` in the ball. -/
private lemma inner_sub_radialProj_nonpos {R : ℝ} (hR : 0 < R) (x z : E) (hz : ‖z‖ ≤ R) :
    inner ℝ (x - radialProj R x) (z - radialProj R x) ≤ 0 := by
  have hc1 : 0 ≤ 1 - R / max R ‖x‖ := sub_nonneg.2 (radialProj_coeff_le_one hR x)
  rw [sub_radialProj, real_inner_smul_left, inner_sub_right, radialProj, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  rcases le_or_gt ‖x‖ R with hx | hx
  · rw [max_eq_left hx, div_self hR.ne', sub_self, zero_mul]
  · have hxpos : 0 < ‖x‖ := hR.trans hx
    have hc : R / max R ‖x‖ * ‖x‖ ^ 2 = R * ‖x‖ := by
      rw [max_eq_right hx.le]
      field_simp
    have hinner : inner ℝ x z ≤ ‖x‖ * R :=
      (real_inner_le_norm x z).trans (mul_le_mul_of_nonneg_left hz (norm_nonneg _))
    rw [hc]
    exact mul_nonpos_of_nonneg_of_nonpos hc1 (by linarith)

/-- The radial projection is `1`-Lipschitz. -/
private lemma norm_radialProj_sub_le {R : ℝ} (hR : 0 < R) (x y : E) :
    ‖radialProj R x - radialProj R y‖ ≤ ‖x - y‖ := by
  set a := radialProj R x
  set b := radialProj R y
  have h1 := inner_sub_radialProj_nonpos hR x b (norm_radialProj_le hR y)
  have h2 := inner_sub_radialProj_nonpos hR y a (norm_radialProj_le hR x)
  have key : x - y = (a - b) + ((x - a) - (y - b)) := by abel
  have hinner : 0 ≤ inner ℝ (a - b) ((x - a) - (y - b)) := by
    have e1 : inner ℝ (a - b) (x - a) = -inner ℝ (x - a) (b - a) := by
      rw [real_inner_comm, ← inner_neg_right, neg_sub]
    have e2 : inner ℝ (a - b) (y - b) = inner ℝ (y - b) (a - b) := real_inner_comm _ _
    rw [inner_sub_right, e1, e2]
    linarith
  have hsq : ‖a - b‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [key, norm_add_sq_real]
    nlinarith [sq_nonneg ‖(x - a) - (y - b)‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

private lemma continuous_radialProj {R : ℝ} (hR : 0 < R) : Continuous (radialProj (E := E) R) :=
  (continuous_const.div (continuous_const.max continuous_norm)
    fun _ => (hR.trans_le (le_max_left _ _)).ne').smul continuous_id

/-- The radial projection as a map into the closed ball. -/
private noncomputable def toBall {R : ℝ} (hR : 0 < R) (x : E) : Metric.closedBall (0 : E) R :=
  ⟨radialProj R x, mem_closedBall_zero_iff.2 (norm_radialProj_le hR x)⟩

private lemma continuous_toBall {R : ℝ} (hR : 0 < R) : Continuous (toBall (E := E) hR) :=
  (continuous_radialProj hR).subtype_mk _

private lemma dist_toBall_le {R : ℝ} (hR : 0 < R) (x y : E) :
    dist (toBall hR x) (toBall hR y) ≤ ‖x - y‖ := by
  rw [Subtype.dist_eq, dist_eq_norm]
  exact norm_radialProj_sub_le hR x y

end RadialProjection

section Duality

/-! ### The dual bound on a ball -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
private lemma compactSpace_closedBall (R : ℝ) : CompactSpace (Metric.closedBall (0 : E) R) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall 0 R)

omit [MeasurableSpace E] [BorelSpace E] in
private lemma exists_abs_le {R : ℝ} {φ : Metric.closedBall (0 : E) R → ℝ} (hφ : Continuous φ) :
    ∃ C, ∀ x, |φ x| ≤ C := by
  have := compactSpace_closedBall (E := E) R
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
  exact ⟨C, fun x => (Real.norm_eq_abs _).symm.trans_le (hC x (Set.mem_univ x))⟩

private lemma integrable_of_continuous {R : ℝ} (ν : Measure (Metric.closedBall (0 : E) R))
    [IsFiniteMeasure ν] {φ : Metric.closedBall (0 : E) R → ℝ} (hφ : Continuous φ) :
    Integrable φ ν := by
  have := compactSpace_closedBall (E := E) R
  exact hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace φ)

/-- **Infimal-convolution inequality for the projected Gaussian.** If
`φ x + ψ y ≤ (1 - t) / 2 * d(x, y)²` on the ball, then `log ∫ e^φ dγ_R ≤ -∫ ψ dγ_R`, where `γ_R`
is the image of the standard Gaussian under the radial projection. This is the Gaussian
Prékopa–Leindler inequality with `w = 1`, `u = e^{t ψ / (1 - t)}` and `v = e^φ` (composed with
the `1`-Lipschitz projection), followed by Jensen's inequality for `u`. -/
private lemma log_integral_exp_le {R : ℝ} (hR : 0 < R) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {φ ψ : Metric.closedBall (0 : E) R → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφψ : ∀ x y, φ x + ψ y ≤ (1 - t) / 2 * dist x y ^ 2) :
    Real.log (∫ x, Real.exp (φ x) ∂((stdGaussian E).map (toBall hR))) ≤
      -∫ x, ψ x ∂((stdGaussian E).map (toBall hR)) := by
  have hp : Measurable (toBall (E := E) hR) := (continuous_toBall hR).measurable
  set γK := (stdGaussian E).map (toBall hR) with hγK
  have h1t : 0 < 1 - t := by linarith
  set s := t / (1 - t) with hs
  have hs1 : s * (1 - t) = t := by rw [hs]; field_simp
  have hA_int : Integrable (fun x => Real.exp (s * ψ x)) γK :=
    integrable_of_continuous γK (continuous_const.mul hψ).rexp
  have hB_int : Integrable (fun x => Real.exp (φ x)) γK :=
    integrable_of_continuous γK hφ.rexp
  set A := ∫ x, Real.exp (s * ψ x) ∂γK with hA
  set B := ∫ x, Real.exp (φ x) ∂γK with hB
  have hApos : 0 < A := integral_exp_pos hA_int
  have hBpos : 0 < B := integral_exp_pos hB_int
  -- the Prékopa–Leindler step
  set u : E → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (s * ψ (toBall hR x))) with hu_def
  set v : E → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (φ (toBall hR y))) with hv_def
  have hu : Measurable u := ENNReal.measurable_ofReal.comp
    ((continuous_const.mul (hψ.comp (continuous_toBall hR))).rexp).measurable
  have hv : Measurable v := ENNReal.measurable_ofReal.comp
    ((hφ.comp (continuous_toBall hR)).rexp).measurable
  have hPL := lintegral_rpow_mul_le_stdGaussian (E := E) ht0 ht1 hu hv (w := fun _ => 1)
    measurable_const (fun x y => by
      simp only [hu_def, hv_def]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le h1t.le,
        ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le ht0.le, ← Real.exp_mul, ← Real.exp_mul,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
        ← Real.exp_add, ← Real.exp_add, ENNReal.ofReal_le_one, Real.exp_le_one_iff]
      have h := mul_le_mul_of_nonneg_left (hφψ (toBall hR y) (toBall hR x)) ht0.le
      have hd : dist (toBall hR y) (toBall hR x) ≤ ‖x - y‖ := by
        rw [← norm_neg, neg_sub]; exact dist_toBall_le hR y x
      have hd2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ dist_nonneg hd 2)
        (by positivity : (0 : ℝ) ≤ t * ((1 - t) / 2))
      have e : s * ψ (toBall hR x) * (1 - t) = t * ψ (toBall hR x) := by
        rw [mul_right_comm, hs1]
      rw [e]
      nlinarith)
  have hlu : ∫⁻ x, u x ∂stdGaussian E = ENNReal.ofReal A := by
    rw [hA, ofReal_integral_eq_lintegral_ofReal hA_int (ae_of_all _ fun _ => (Real.exp_pos _).le),
      hγK, lintegral_map (f := fun x => ENNReal.ofReal (Real.exp (s * ψ x)))
        (ENNReal.continuous_ofReal.comp (continuous_const.mul hψ).rexp).measurable hp]
  have hlv : ∫⁻ x, v x ∂stdGaussian E = ENNReal.ofReal B := by
    rw [hB, ofReal_integral_eq_lintegral_ofReal hB_int (ae_of_all _ fun _ => (Real.exp_pos _).le),
      hγK, lintegral_map (f := fun x => ENNReal.ofReal (Real.exp (φ x)))
        (ENNReal.continuous_ofReal.comp hφ.rexp).measurable hp]
  rw [hlu, hlv, lintegral_const, measure_univ, mul_one,
    ENNReal.ofReal_rpow_of_nonneg hApos.le h1t.le, ENNReal.ofReal_rpow_of_nonneg hBpos.le ht0.le,
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_one] at hPL
  have hlog : (1 - t) * Real.log A + t * Real.log B ≤ 0 := by
    have h := Real.log_le_log (by positivity) hPL
    rwa [Real.log_one, Real.log_mul (by positivity) (by positivity), Real.log_rpow hApos,
      Real.log_rpow hBpos] at h
  -- Jensen's inequality for `exp`
  have hJ : Real.exp (∫ x, s * ψ x ∂γK) ≤ A :=
    convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all _ fun _ => Set.mem_univ _) (integrable_of_continuous γK (continuous_const.mul hψ))
      hA_int
  rw [integral_const_mul] at hJ
  have hJ' : s * ∫ x, ψ x ∂γK ≤ Real.log A := (Real.le_log_iff_exp_le hApos).2 hJ
  have h2 : t * (∫ x, ψ x ∂γK) + t * Real.log B ≤ 0 := by
    have := mul_le_mul_of_nonneg_left hJ' h1t.le
    rw [← mul_assoc, mul_comm (1 - t) s, hs1] at this
    linarith
  have h3 : t * Real.log B ≤ t * -∫ x, ψ x ∂γK := by linarith
  exact le_of_mul_le_mul_left h3 ht0

/-- **The dual bound.** For continuous `φ, ψ` on the ball with `φ x + ψ y ≤ d(x, y)²`,
`(1 - t) / 2 * (∫ φ dμ_R + ∫ ψ dγ_R) ≤ KL(μ ‖ γ)`, where `μ_R` and `γ_R` are the images of `μ`
and of the standard Gaussian `γ` under the radial projection: the Donsker–Varadhan inequality
for `(1 - t) / 2 * φ`, the infimal-convolution inequality and the data processing inequality
`KL(μ_R ‖ γ_R) ≤ KL(μ ‖ γ)`. -/
private lemma dual_bound {R : ℝ} (hR : 0 < R) (μ : ProbabilityMeasure E)
    (hKL : InformationTheory.klDiv (μ : Measure E) (stdGaussian E) ≠ ⊤) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) {φ ψ : Metric.closedBall (0 : E) R → ℝ} (hφ : Continuous φ)
    (hψ : Continuous ψ) (hφψ : ∀ x y, φ x + ψ y ≤ dist x y ^ 2) :
    (1 - t) / 2 * (∫ x, φ x ∂((μ : Measure E).map (toBall hR)) +
      ∫ y, ψ y ∂((stdGaussian E).map (toBall hR))) ≤
      (InformationTheory.klDiv (μ : Measure E) (stdGaussian E)).toReal := by
  have hp : Measurable (toBall (E := E) hR) := (continuous_toBall hR).measurable
  have ha : 0 < (1 - t) / 2 := by linarith
  have hC := log_integral_exp_le hR ht0 ht1 (continuous_const.mul hφ) (continuous_const.mul hψ)
    (φ := fun x => (1 - t) / 2 * φ x) (ψ := fun y => (1 - t) / 2 * ψ y) (fun x y => by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (hφψ x y) ha.le)
  have hmap := InformationTheory.klDiv_map_le (μ : Measure E) (stdGaussian E) hp
  obtain ⟨C, hC'⟩ := exists_abs_le (φ := fun x => (1 - t) / 2 * φ x) (continuous_const.mul hφ)
  have hDV :=
    MathlibExt.InformationTheory.DonskerVaradhan.integral_sub_log_integral_exp_le_toReal_klDiv
      (f := fun x => (1 - t) / 2 * φ x) (ne_top_of_le_ne_top hKL hmap)
      (continuous_const.mul hφ).measurable hC'
  have hmono := ENNReal.toReal_mono hKL hmap
  simp only [integral_const_mul] at hDV hC
  rw [mul_add]
  linarith

end Duality

section TransportCost

/-! ### Talagrand's inequality for the projected measures -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open MathlibExt.Probability.GaussianLogSobolevWanted (lintegral_rpow_mul_le_stdGaussian)
open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (primalValues
  kantorovich_duality_compact)

/-- **Talagrand's inequality for the projected measures.** The images `μ_R` and `γ_R` of `μ` and
of the standard Gaussian under the radial projection onto the ball of radius `R` satisfy
`W₂(μ_R, γ_R)² ≤ 2 KL(μ ‖ γ)`: Kantorovich duality on the compact ball turns the dual bound into
`W₂(μ_R, γ_R)² ≤ 2 KL(μ ‖ γ) / (1 - t)` for every `t ∈ (0, 1)`. -/
private lemma transportCost_map_radialProj_le {R : ℝ} (hR : 0 < R) (μ : ProbabilityMeasure E)
    (hKL : InformationTheory.klDiv (μ : Measure E) (stdGaussian E) ≠ ⊤) :
    transportCost 2 (μ.map (radialProj R))
      (ProbabilityMeasure.map ⟨stdGaussian E, inferInstance⟩ (radialProj R)) ≤
      2 * InformationTheory.klDiv (μ : Measure E) (stdGaussian E) := by
  have := compactSpace_closedBall (E := E) R
  have : Nonempty (Metric.closedBall (0 : E) R) := ⟨⟨0, Metric.mem_closedBall_self hR.le⟩⟩
  have hp : Measurable (toBall (E := E) hR) := (continuous_toBall hR).measurable
  set γ : ProbabilityMeasure E := ⟨stdGaussian E, inferInstance⟩ with hγ
  set μK : ProbabilityMeasure (Metric.closedBall (0 : E) R) := μ.map (toBall hR) with hμK
  set γK : ProbabilityMeasure (Metric.closedBall (0 : E) R) := γ.map (toBall hR) with hγK
  set c : Metric.closedBall (0 : E) R × Metric.closedBall (0 : E) R → ℝ :=
    fun z => dist z.1 z.2 ^ 2 with hc_def
  have hc : Continuous c := (continuous_fst.dist continuous_snd).pow 2
  set H := (InformationTheory.klDiv (μ : Measure E) (stdGaussian E)).toReal with hH
  have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
  have hdual := kantorovich_duality_compact μK γK c hc
  -- the dual values are at most `2 H / (1 - t)`
  have hbound : ∀ t : ℝ, 0 < t → t < 1 → sInf (primalValues μK γK c) ≤ 2 * H / (1 - t) := by
    intro t ht0 ht1
    rw [hdual]
    refine csSup_le ⟨0, 0, 0, ⟨continuous_const, continuous_const, fun x y => ?_⟩, ?_⟩ ?_
    · simp only [hc_def, Pi.zero_apply, add_zero]
      positivity
    · simp
    · rintro r ⟨φ, ψ, ⟨hφ, hψ, hle⟩, rfl⟩
      have h := dual_bound hR μ hKL ht0 ht1 hφ hψ hle
      rw [le_div_iff₀ (by linarith)]
      have e1 : (μK : Measure _) = (μ : Measure E).map (toBall hR) := rfl
      have e2 : (γK : Measure _) = (stdGaussian E).map (toBall hR) := rfl
      rw [e1, e2]
      linarith
  -- let `t → 0`
  have hP : sInf (primalValues μK γK c) ≤ 2 * H := by
    have htend : Tendsto (fun t : ℝ => 2 * H / (1 - t)) (𝓝[>] 0) (𝓝 (2 * H)) := by
      have h : Tendsto (fun t : ℝ => 2 * H / (1 - t)) (𝓝 0) (𝓝 (2 * H / (1 - 0))) :=
        tendsto_const_nhds.div (tendsto_const_nhds.sub tendsto_id) (by norm_num)
      rw [sub_zero, div_one] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hbound t ht.1 ht.2
  have hne : (primalValues μK γK c).Nonempty :=
    ⟨_, μK.prod γK, MathlibExt.MeasureTheory.OptimalTransport.Wasserstein.isCoupling_prod μK γK,
      rfl⟩
  have h2KL : 2 * InformationTheory.klDiv (μ : Measure E) (stdGaussian E) =
      ENNReal.ofReal (2 * H) := by
    rw [ENNReal.ofReal_mul (by norm_num), hH, ENNReal.ofReal_toReal hKL]
    norm_num
  rw [h2KL]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < ε := hε
  obtain ⟨r, ⟨π, hπ, rfl⟩, hr⟩ := exists_lt_of_csInf_lt hne
    (show sInf (primalValues μK γK c) < 2 * H + ε by linarith)
  -- push the coupling of `μ_K` and `γ_K` forward to `E × E`
  have hg : Measurable fun z : Metric.closedBall (0 : E) R × Metric.closedBall (0 : E) R =>
      ((z.1 : E), (z.2 : E)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd)
  set πE : ProbabilityMeasure (E × E) := π.map fun z => ((z.1 : E), (z.2 : E)) with hπE
  have hcoup : IsCoupling (μ.map (radialProj R))
      (γ.map (radialProj R)) πE := by
    obtain ⟨h1, h2⟩ := hπ
    refine ⟨?_, ?_⟩
    · rw [ProbabilityMeasure.toMeasure_map, hπE, ProbabilityMeasure.toMeasure_map,
        Measure.map_map measurable_fst hg,
        show (Prod.fst ∘ fun z : Metric.closedBall (0 : E) R × Metric.closedBall (0 : E) R =>
          ((z.1 : E), (z.2 : E))) = Subtype.val ∘ Prod.fst from rfl,
        ← Measure.map_map measurable_subtype_coe measurable_fst, ← h1, hμK,
        ProbabilityMeasure.toMeasure_map, Measure.map_map measurable_subtype_coe hp]
      rfl
    · rw [ProbabilityMeasure.toMeasure_map, hπE, ProbabilityMeasure.toMeasure_map,
        Measure.map_map measurable_snd hg,
        show (Prod.snd ∘ fun z : Metric.closedBall (0 : E) R × Metric.closedBall (0 : E) R =>
          ((z.1 : E), (z.2 : E))) = Subtype.val ∘ Prod.snd from rfl,
        ← Measure.map_map measurable_subtype_coe measurable_snd, ← h2, hγK,
        ProbabilityMeasure.toMeasure_map, Measure.map_map measurable_subtype_coe hp]
      rfl
  calc transportCost 2 _ _ ≤ ∫⁻ z, edist z.1 z.2 ^ (2 : ℝ) ∂(πE : Measure (E × E)) :=
        MathlibExt.MeasureTheory.OptimalTransport.Wasserstein.transportCost_le_of_isCoupling hcoup
    _ = ENNReal.ofReal (∫ z, c z ∂(π : Measure _)) := by
        rw [hπE, ProbabilityMeasure.toMeasure_map, lintegral_map (measurable_edist.pow_const _) hg,
          ofReal_integral_eq_lintegral_ofReal
            (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace c))
            (ae_of_all _ fun z => by positivity)]
        refine lintegral_congr fun z => ?_
        rw [edist_dist, ← Subtype.dist_eq, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num)]
        norm_cast
    _ ≤ ENNReal.ofReal (2 * H + ε) := ENNReal.ofReal_le_ofReal hr.le
    _ = ENNReal.ofReal (2 * H) + ε := by
        rw [ENNReal.ofReal_add (by positivity) ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]

end TransportCost

section Approximation

/-! ### Approximation by the projected measures -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E]

/-- For a measure with finite second moment, the cost `∫ d(x, P_R x)² dν` of the radial
projection onto the ball of radius `R = n + 1` tends to `0`. -/
private lemma tendsto_lintegral_edist_radialProj (ν : Measure E)
    (hν : ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂ν < ∞) :
    Tendsto (fun n : ℕ => ∫⁻ x, edist x (radialProj ((n : ℝ) + 1) x) ^ (2 : ℝ) ∂ν) atTop
      (𝓝 0) := by
  have hR : ∀ n : ℕ, (0 : ℝ) < n + 1 := fun n => by positivity
  have hmeas : ∀ n : ℕ, Measurable fun x : E => edist x (radialProj ((n : ℝ) + 1) x) ^ (2 : ℝ) :=
    fun n => (continuous_id.edist (continuous_radialProj (hR n))).measurable.pow_const _
  have hbound : ∀ (n : ℕ) (x : E),
      edist x (radialProj ((n : ℝ) + 1) x) ^ (2 : ℝ) ≤ ‖x‖ₑ ^ (2 : ℝ) := by
    intro n x
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [edist_dist, dist_eq_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_sub_radialProj_le (hR n) x)
  have hlim : ∀ x : E,
      Tendsto (fun n : ℕ => edist x (radialProj ((n : ℝ) + 1) x) ^ (2 : ℝ)) atTop (𝓝 0) := by
    intro x
    refine (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
    have hx : ‖x‖ ≤ (n : ℝ) + 1 := by
      have h1 := Nat.le_ceil ‖x‖
      have h2 : (⌈‖x‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [radialProj_of_norm_le (hR n) hx, edist_self, ENNReal.zero_rpow_of_pos (by norm_num)]
  have h := tendsto_lintegral_of_dominated_convergence (μ := ν) (fun x => ‖x‖ₑ ^ (2 : ℝ))
    (F := fun n x => edist x (radialProj ((n : ℝ) + 1) x) ^ (2 : ℝ)) (f := fun _ => 0) hmeas
    (fun n => ae_of_all _ (hbound n)) hν.ne (ae_of_all _ hlim)
  simpa using h

end Approximation

/-- **Talagrand's transport inequality for the Gaussian measure.** Let `γ` be the standard
Gaussian measure on a finite-dimensional real inner product space `E`. For every probability
measure `μ` on `E` with finite second moment, `W_2(μ, γ)² ≤ 2 H_γ(μ)`, where
`H_γ(μ) = KL(μ ‖ γ)` is the relative entropy (`+∞` unless `μ ≪ γ`): `γ` satisfies `T_2(1)`,
with a constant independent of the dimension (C. Villani, *Optimal Transport: Old and New*,
Springer 2009, Example 22.15 with Definition 22.1; originally M. Talagrand, Geom. Funct. Anal.
6 (1996) 587–600). -/
theorem talagrand_stdGaussian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : ProbabilityMeasure E) (hμ : ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂(μ : Measure E) < ∞) :
    wasserstein 2 μ ⟨stdGaussian E, inferInstance⟩ ^ (2 : ℝ) ≤
      2 * InformationTheory.klDiv (μ : Measure E) (stdGaussian E) := by
  set γ : ProbabilityMeasure E := ⟨stdGaussian E, inferInstance⟩ with hγ
  by_cases hKL : InformationTheory.klDiv (μ : Measure E) (stdGaussian E) = ⊤
  · rw [hKL, ENNReal.mul_top (by norm_num)]
    exact le_top
  set B := (2 * InformationTheory.klDiv (μ : Measure E) (stdGaussian E)) ^ (1 / 2 : ℝ) with hB
  have hγ2 : ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂(stdGaussian E) < ∞ := by
    have h := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top (p := 2) two_ne_zero
      ENNReal.ofNat_ne_top (IsGaussian.memLp_two_id (μ := stdGaussian E)).eLpNorm_lt_top
    simpa using h
  set a : ℕ → ℝ≥0∞ := fun n =>
    (∫⁻ x, edist x (radialProj ((n : ℝ) + 1) x) ^ (2 : ℝ) ∂(μ : Measure E)) ^ (1 / 2 : ℝ) with ha
  set b : ℕ → ℝ≥0∞ := fun n =>
    (∫⁻ x, edist x (radialProj ((n : ℝ) + 1) x) ^ (2 : ℝ) ∂(stdGaussian E)) ^ (1 / 2 : ℝ) with hb
  -- `W₂(μ, γ) ≤ W₂(μ, μ_R) + W₂(μ_R, γ_R) + W₂(γ_R, γ)` with `R = n + 1`
  have key : ∀ n : ℕ, wasserstein 2 μ γ ≤ a n + B + b n := by
    intro n
    have hR : (0 : ℝ) < n + 1 := by positivity
    have hPm := (continuous_radialProj (E := E) hR).measurable
    have h1 : wasserstein 2 μ (μ.map (radialProj ((n : ℝ) + 1))) ≤ a n := by
      have hd : Measurable fun x : E => (x, radialProj ((n : ℝ) + 1) x) :=
        measurable_id.prodMk hPm
      have hcoup : IsCoupling μ (μ.map (radialProj ((n : ℝ) + 1)))
          (μ.map fun x => (x, radialProj ((n : ℝ) + 1) x)) := by
        refine ⟨?_, ?_⟩
        · rw [ProbabilityMeasure.toMeasure_map, Measure.map_map measurable_fst hd]
          exact Measure.map_id.symm
        · rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
            Measure.map_map measurable_snd hd]
          rfl
      refine (wasserstein_le_of_isCoupling (by norm_num) hcoup).trans_eq ?_
      rw [ProbabilityMeasure.toMeasure_map, lintegral_map (measurable_edist.pow_const _) hd]
    have h2 : wasserstein 2 (μ.map (radialProj ((n : ℝ) + 1)))
        (γ.map (radialProj ((n : ℝ) + 1))) ≤ B :=
      ENNReal.rpow_le_rpow (transportCost_map_radialProj_le hR μ hKL) (by norm_num)
    have h3 : wasserstein 2 (γ.map (radialProj ((n : ℝ) + 1))) γ ≤ b n := by
      have hd : Measurable fun x : E => (radialProj ((n : ℝ) + 1) x, x) :=
        hPm.prodMk measurable_id
      have hcoup : IsCoupling (γ.map (radialProj ((n : ℝ) + 1))) γ
          (γ.map fun x => (radialProj ((n : ℝ) + 1) x, x)) := by
        refine ⟨?_, ?_⟩
        · rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
            Measure.map_map measurable_fst hd]
          rfl
        · rw [ProbabilityMeasure.toMeasure_map, Measure.map_map measurable_snd hd]
          exact Measure.map_id.symm
      refine (wasserstein_le_of_isCoupling (by norm_num) hcoup).trans_eq ?_
      rw [ProbabilityMeasure.toMeasure_map, lintegral_map (measurable_edist.pow_const _) hd]
      simp_rw [edist_comm (radialProj _ _)]
      rfl
    calc wasserstein 2 μ γ
        ≤ wasserstein 2 μ (μ.map (radialProj ((n : ℝ) + 1))) +
            wasserstein 2 (μ.map (radialProj ((n : ℝ) + 1))) γ :=
          wasserstein_triangle (p := 2) (by norm_num) _ _ _
      _ ≤ wasserstein 2 μ (μ.map (radialProj ((n : ℝ) + 1))) +
            (wasserstein 2 (μ.map (radialProj ((n : ℝ) + 1))) (γ.map (radialProj ((n : ℝ) + 1))) +
              wasserstein 2 (γ.map (radialProj ((n : ℝ) + 1))) γ) :=
          add_le_add le_rfl (wasserstein_triangle (p := 2) (by norm_num) _ _ _)
      _ ≤ a n + (B + b n) := add_le_add h1 (add_le_add h2 h3)
      _ = a n + B + b n := (add_assoc _ _ _).symm
  -- let `R → ∞`
  have hhalf : (0 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
  have ha' : Tendsto a atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0).comp
      (tendsto_lintegral_edist_radialProj (μ : Measure E) hμ)
    rwa [hhalf] at h
  have hb' : Tendsto b atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0).comp
      (tendsto_lintegral_edist_radialProj (stdGaussian E) hγ2)
    rwa [hhalf] at h
  have hlim : Tendsto (fun n => a n + B + b n) atTop (𝓝 (0 + B + 0)) :=
    (ha'.add tendsto_const_nhds).add hb'
  rw [zero_add, add_zero] at hlim
  have hW : wasserstein 2 μ γ ≤ B := ge_of_tendsto' hlim key
  calc wasserstein 2 μ γ ^ (2 : ℝ) ≤ B ^ (2 : ℝ) := ENNReal.rpow_le_rpow hW (by norm_num)
    _ = 2 * InformationTheory.klDiv (μ : Measure E) (stdGaussian E) := by
      rw [hB, ← ENNReal.rpow_mul]
      norm_num

end MathlibExt.Probability.TalagrandTransportWanted
