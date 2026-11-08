/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.StrongLaw

/-!
# Fisher information, the Cramér–Rao bound, and consistency of maximum likelihood

A one-parameter statistical model is a family of densities `p θ` (`θ ∈ ℝ`) with respect to a
reference measure `ν` on a sample space `𝓧`. Its **Fisher information** at `θ` is
`I(θ) = ∫ (∂_θ p θ x)² / p θ x dν(x)` (`fisherInformation`). The **Cramér–Rao inequality**
says that an estimator `T` that is unbiased for `g θ` on a neighborhood of `θ` has variance at
least `g'(θ)² / I(θ)`, provided differentiation under the integral sign is allowed.

**Wald's theorem** (consistency of maximum likelihood), in the form of Ferguson (1996,
Theorem 17) for positive densities: for a compact metric parameter space, densities continuous
in the parameter, an identifiable model and an integrable upper envelope of the log-likelihood
ratios, every sequence of maximizers of the sample log-likelihood of an i.i.d. sample from
`p θ₀` converges to `θ₀` almost surely.

## Main results

* `sq_deriv_le_fisherInformation_mul`, `cramerRao_general`, `cramerRao`: the Cramér–Rao
  inequality, in multiplicative form (`g'(θ)² ≤ I(θ) Var_θ T`) and quotient form.
* `ae_tendsto_maximumLikelihood`: Wald's consistency theorem.

## References

* H. Cramér, *Mathematical Methods of Statistics* (1946), ch. 32.
* C. R. Rao, "Information and the accuracy attainable in the estimation of statistical
  parameters", Bull. Calcutta Math. Soc. 37 (1945) 81–91.
* A. Wald, "Note on the consistency of the maximum likelihood estimate", Ann. Math. Statist.
  20 (1949) 595–601.
* T. S. Ferguson, *A Course in Large Sample Theory* (1996), Theorem 17.
* E. L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed. (1998), ch. 2.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.FisherInformation

open MeasureTheory ProbabilityTheory Filter Topology

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **Fisher information** at `θ` of the one-parameter family of densities `p θ` with
respect to `ν`: `∫ (∂_θ p θ x)² / p θ x dν(x)`. Points with `p θ x = 0` contribute `0` (for a
nonnegative family, `∂_θ p θ x = 0` there). -/
noncomputable def fisherInformation (ν : Measure 𝓧) (p : ℝ → 𝓧 → ℝ) (θ : ℝ) : ℝ :=
  ∫ x, deriv (fun θ' => p θ' x) θ ^ 2 / p θ x ∂ν

/-- The probability law with density `p θ` with respect to `ν`. -/
noncomputable def lawOf {Θ : Type*} (ν : Measure 𝓧) (p : Θ → 𝓧 → ℝ) (θ : Θ) : Measure 𝓧 :=
  ν.withDensity fun x => ENNReal.ofReal (p θ x)

/-- Cauchy–Schwarz for real integrals, via the discriminant. -/
private theorem integral_mul_sq_le {ν : Measure 𝓧} {a b : 𝓧 → ℝ}
    (ha : Integrable (fun x => a x ^ 2) ν) (hb : Integrable (fun x => b x ^ 2) ν)
    (hab : Integrable (fun x => a x * b x) ν) :
    (∫ x, a x * b x ∂ν) ^ 2 ≤ (∫ x, a x ^ 2 ∂ν) * ∫ x, b x ^ 2 ∂ν := by
  have h := discrim_le_zero (K := ℝ) (a := ∫ x, b x ^ 2 ∂ν) (b := 2 * ∫ x, a x * b x ∂ν)
    (c := ∫ x, a x ^ 2 ∂ν) fun t => by
      have hi : ∫ x, (a x + t * b x) ^ 2 ∂ν =
          (∫ x, b x ^ 2 ∂ν) * (t * t) + 2 * (∫ x, a x * b x ∂ν) * t + ∫ x, a x ^ 2 ∂ν := by
        have e : (fun x => (a x + t * b x) ^ 2) =
            fun x => (t * t) * b x ^ 2 + (2 * t) * (a x * b x) + a x ^ 2 := by
          funext x; ring
        have h1 : Integrable (fun x => (t * t) * b x ^ 2) ν := hb.const_mul _
        have h2 : Integrable (fun x => (2 * t) * (a x * b x)) ν := hab.const_mul _
        have h12 : Integrable (fun x => (t * t) * b x ^ 2 + (2 * t) * (a x * b x)) ν := h1.add h2
        rw [e, integral_add h12 ha, integral_add h1 h2, integral_const_mul,
          integral_const_mul]
        ring
      rw [← hi]
      exact integral_nonneg fun x => sq_nonneg _
  rw [discrim] at h
  nlinarith

/-- A product of two square-integrable real functions is integrable (`|ab| ≤ (a² + b²)/2`). -/
private theorem integrable_mul_of_sq {ν : Measure 𝓧} {a b : 𝓧 → ℝ}
    (ha : Integrable (fun x => a x ^ 2) ν) (hb : Integrable (fun x => b x ^ 2) ν)
    (hm : AEStronglyMeasurable (fun x => a x * b x) ν) :
    Integrable (fun x => a x * b x) ν := by
  refine Integrable.mono' ((ha.add hb).div_const 2) hm (Eventually.of_forall fun x => ?_)
  change ‖a x * b x‖ ≤ (a x ^ 2 + b x ^ 2) / 2
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|a x| - |b x|), sq_abs (a x), sq_abs (b x)]

/-- **Cramér–Rao inequality, multiplicative form**: under the hypotheses of `cramerRao_general`,
`g'(θ)² ≤ I(θ) · Var_θ T`. Unlike the quotient form, this is informative when `I(θ) = 0`: it then
says `g'(θ) = 0`.

Source: Cramér (1946), ch. 32; Rao (1945); Lehmann & Casella (1998), ch. 2. -/
theorem sq_deriv_le_fisherInformation_mul {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {T : 𝓧 → ℝ}
    {g : ℝ → ℝ} {θ : ℝ}
    (hp_nonneg : ∀ θ' x, 0 ≤ p θ' x)
    (hp_int : ∀ᶠ θ' in 𝓝 θ, ∫ x, p θ' x ∂ν = 1)
    (hs_meas : AEStronglyMeasurable (fun x => deriv (fun θ' => p θ' x) θ) ν)
    (hI_int : Integrable (fun x => deriv (fun θ' => p θ' x) θ ^ 2 / p θ x) ν)
    (hT_meas : AEStronglyMeasurable T ν)
    (hT_sq : Integrable (fun x => T x ^ 2 * p θ x) ν)
    (h_unbiased : ∀ᶠ θ' in 𝓝 θ, ∫ x, T x * p θ' x ∂ν = g θ')
    (h_deriv_one : HasDerivAt (fun θ' => ∫ x, p θ' x ∂ν)
      (∫ x, deriv (fun θ' => p θ' x) θ ∂ν) θ)
    (h_deriv_T : HasDerivAt (fun θ' => ∫ x, T x * p θ' x ∂ν)
      (∫ x, T x * deriv (fun θ' => p θ' x) θ ∂ν) θ) :
    deriv g θ ^ 2 ≤ fisherInformation ν p θ * ∫ x, (T x - g θ) ^ 2 * p θ x ∂ν := by
  set s : 𝓧 → ℝ := fun x => deriv (fun θ' => p θ' x) θ with hs_def
  set c := g θ
  -- `p θ` is integrable since its integral is `1`.
  have hp1 : ∫ x, p θ x ∂ν = 1 := hp_int.self_of_nhds
  have hpI : Integrable (p θ) ν := by
    by_contra h
    rw [integral_undef h] at hp1
    exact zero_ne_one hp1
  -- the score vanishes where the density does
  have hs0 : ∀ x, p θ x = 0 → s x = 0 := fun x hx => by
    have : IsLocalMin (fun θ' => p θ' x) θ :=
      Eventually.of_forall fun θ' => by simp only; rw [hx]; exact hp_nonneg θ' x
    exact this.deriv_eq_zero
  set r : 𝓧 → ℝ := fun x => Real.sqrt (p θ x)
  set b : 𝓧 → ℝ := fun x => s x / r x
  have hr_sq : ∀ x, r x ^ 2 = p θ x := fun x => Real.sq_sqrt (hp_nonneg θ x)
  have hb_sq : ∀ x, b x ^ 2 = s x ^ 2 / p θ x := fun x => by
    simp only [b, div_pow, hr_sq]
  have hrb : ∀ x, r x * b x = s x := fun x => by
    by_cases hx : p θ x = 0
    · simp [b, r, hx, hs0 x hx]
    · have : r x ≠ 0 := by
        simp only [r]; exact (Real.sqrt_pos.2 (lt_of_le_of_ne (hp_nonneg θ x) (Ne.symm hx))).ne'
      simp only [b]
      rw [mul_div_assoc', mul_div_cancel_left₀ _ this]
  have hr_meas : AEStronglyMeasurable r ν :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hpI.aestronglyMeasurable
  have hb_meas : AEStronglyMeasurable b ν :=
    (hs_meas.aemeasurable.div hr_meas.aemeasurable).aestronglyMeasurable
  have hr2 : Integrable (fun x => r x ^ 2) ν := by simp_rw [hr_sq]; exact hpI
  have hb2 : Integrable (fun x => b x ^ 2) ν := by simp_rw [hb_sq]; exact hI_int
  set a : 𝓧 → ℝ := fun x => T x * r x
  have ha2 : Integrable (fun x => a x ^ 2) ν := by
    simp_rw [a, mul_pow, hr_sq]; exact hT_sq
  have ha_meas : AEStronglyMeasurable a ν := hT_meas.mul hr_meas
  -- integrability of the products
  have hTs : Integrable (fun x => T x * s x) ν := by
    have := integrable_mul_of_sq ha2 hb2 (ha_meas.mul hb_meas)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [a, ← hrb x]; ring
  have hsI : Integrable s ν := by
    have := integrable_mul_of_sq hr2 hb2 (hr_meas.mul hb_meas)
    exact this.congr (Eventually.of_forall hrb)
  have hTp : Integrable (fun x => T x * p θ x) ν := by
    have := integrable_mul_of_sq ha2 hr2 (ha_meas.mul hr_meas)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [a]; rw [← hr_sq x]; ring
  -- the derivative identities
  have hs_int0 : ∫ x, s x ∂ν = 0 := by
    have h1 : HasDerivAt (fun θ' => ∫ x, p θ' x ∂ν) 0 θ :=
      (hasDerivAt_const θ (1 : ℝ)).congr_of_eventuallyEq hp_int
    exact h_deriv_one.unique h1
  have hg' : deriv g θ = ∫ x, T x * s x ∂ν := by
    have : HasDerivAt g (∫ x, T x * s x ∂ν) θ :=
      h_deriv_T.congr_of_eventuallyEq (h_unbiased.mono fun θ' h => h.symm)
    exact this.deriv
  set d : 𝓧 → ℝ := fun x => (T x - c) * r x
  have hd2 : Integrable (fun x => d x ^ 2) ν := by
    have e : (fun x => d x ^ 2) =
        fun x => T x ^ 2 * p θ x - 2 * c * (T x * p θ x) + c ^ 2 * p θ x := by
      funext x; simp only [d, mul_pow, hr_sq]; ring
    rw [e]; exact (hT_sq.sub (hTp.const_mul _)).add (hpI.const_mul _)
  have hdb : Integrable (fun x => d x * b x) ν :=
    integrable_mul_of_sq hd2 hb2
      (((hT_meas.sub aestronglyMeasurable_const).mul hr_meas).mul hb_meas)
  have hdb_eq : ∫ x, d x * b x ∂ν = deriv g θ := by
    have e : (fun x => d x * b x) = fun x => T x * s x - c * s x := by
      funext x; simp only [d]; rw [mul_assoc, hrb]; ring
    rw [e, integral_sub hTs (hsI.const_mul _), integral_const_mul, hs_int0, hg']; ring
  have hd2_eq : ∫ x, d x ^ 2 ∂ν = ∫ x, (T x - c) ^ 2 * p θ x ∂ν := by
    congr 1; funext x; simp only [d, mul_pow, hr_sq]
  have hb2_eq : ∫ x, b x ^ 2 ∂ν = fisherInformation ν p θ := by
    simp only [fisherInformation, hb_sq]
    rfl
  have key := integral_mul_sq_le hd2 hb2 hdb
  rw [hdb_eq, hd2_eq, hb2_eq] at key
  linarith [key, mul_comm (fisherInformation ν p θ) (∫ x, (T x - c) ^ 2 * p θ x ∂ν)]

/-- **Cramér–Rao inequality**, with only the hypotheses the proof needs. Let `p θ'` be
nonnegative probability densities with respect to `ν` for `θ'` near `θ`, with square-integrable
score at `θ`, and let `T` be an estimator with finite second moment under `p θ` that is unbiased
for `g θ'` near `θ`. If `∫ p θ' dν` and `∫ T p θ' dν` can be differentiated under the integral
sign at `θ`, then `g'(θ)² / I(θ) ≤ Var_θ T`. When `I(θ) = 0` the left side is the junk value
`0` and the statement is trivial; the informative case is `0 < I(θ)`.

Source: Cramér (1946), ch. 32; Rao (1945); Lehmann & Casella (1998), ch. 2. -/
theorem cramerRao_general {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {T : 𝓧 → ℝ} {g : ℝ → ℝ} {θ : ℝ}
    (hp_nonneg : ∀ θ' x, 0 ≤ p θ' x)
    (hp_int : ∀ᶠ θ' in 𝓝 θ, ∫ x, p θ' x ∂ν = 1)
    (hs_meas : AEStronglyMeasurable (fun x => deriv (fun θ' => p θ' x) θ) ν)
    (hI_int : Integrable (fun x => deriv (fun θ' => p θ' x) θ ^ 2 / p θ x) ν)
    (hT_meas : AEStronglyMeasurable T ν)
    (hT_sq : Integrable (fun x => T x ^ 2 * p θ x) ν)
    (h_unbiased : ∀ᶠ θ' in 𝓝 θ, ∫ x, T x * p θ' x ∂ν = g θ')
    (h_deriv_one : HasDerivAt (fun θ' => ∫ x, p θ' x ∂ν)
      (∫ x, deriv (fun θ' => p θ' x) θ ∂ν) θ)
    (h_deriv_T : HasDerivAt (fun θ' => ∫ x, T x * p θ' x ∂ν)
      (∫ x, T x * deriv (fun θ' => p θ' x) θ ∂ν) θ) :
    deriv g θ ^ 2 / fisherInformation ν p θ ≤ ∫ x, (T x - g θ) ^ 2 * p θ x ∂ν := by
  have h := sq_deriv_le_fisherInformation_mul hp_nonneg hp_int hs_meas hI_int hT_meas hT_sq
    h_unbiased h_deriv_one h_deriv_T
  have hI0 : 0 ≤ fisherInformation ν p θ :=
    integral_nonneg fun x => div_nonneg (sq_nonneg _) (hp_nonneg θ x)
  have hV0 : 0 ≤ ∫ x, (T x - g θ) ^ 2 * p θ x ∂ν :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hp_nonneg θ x)
  rcases hI0.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; exact hV0
  · rw [div_le_iff₀ hpos]; linarith [h, mul_comm (fisherInformation ν p θ)
      (∫ x, (T x - g θ) ^ 2 * p θ x ∂ν)]

set_option linter.unusedVariables false in
/-- **Cramér–Rao inequality.** Let `p θ'` be probability densities with respect to `ν` for
`θ'` near `θ`, differentiable in the parameter at `θ`, with finite positive Fisher information
`I(θ)`, and let `T` be an estimator with finite second moment that is unbiased for `g θ'` near
`θ`. If `∫ p θ' dν` and `∫ T p θ' dν` can be differentiated under the integral sign at `θ`,
then `Var_θ T ≥ g'(θ)² / I(θ)`. The hypotheses `hp_meas`, `hp_diff` and `hI_pos` are not
needed; see `cramerRao_general`.

Source: Cramér (1946), ch. 32; Rao (1945); Lehmann & Casella (1998), ch. 2.
Proves the deferred entry `cramerRao`. -/
theorem cramerRao {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {T : 𝓧 → ℝ} {g : ℝ → ℝ} {θ : ℝ}
    (hp_nonneg : ∀ θ' x, 0 ≤ p θ' x)
    (hp_meas : AEStronglyMeasurable (p θ) ν)
    (hp_int : ∀ᶠ θ' in 𝓝 θ, ∫ x, p θ' x ∂ν = 1)
    (hp_diff : ∀ x, DifferentiableAt ℝ (fun θ' => p θ' x) θ)
    (hs_meas : AEStronglyMeasurable (fun x => deriv (fun θ' => p θ' x) θ) ν)
    (hI_int : Integrable (fun x => deriv (fun θ' => p θ' x) θ ^ 2 / p θ x) ν)
    (hI_pos : 0 < fisherInformation ν p θ)
    (hT_meas : AEStronglyMeasurable T ν)
    (hT_sq : Integrable (fun x => T x ^ 2 * p θ x) ν)
    (h_unbiased : ∀ᶠ θ' in 𝓝 θ, ∫ x, T x * p θ' x ∂ν = g θ')
    (h_deriv_one : HasDerivAt (fun θ' => ∫ x, p θ' x ∂ν)
      (∫ x, deriv (fun θ' => p θ' x) θ ∂ν) θ)
    (h_deriv_T : HasDerivAt (fun θ' => ∫ x, T x * p θ' x ∂ν)
      (∫ x, T x * deriv (fun θ' => p θ' x) θ ∂ν) θ) :
    deriv g θ ^ 2 / fisherInformation ν p θ ≤ ∫ x, (T x - g θ) ^ 2 * p θ x ∂ν :=
  cramerRao_general hp_nonneg hp_int hs_meas hI_int hT_meas hT_sq h_unbiased h_deriv_one
    h_deriv_T

/-- Integrals against `lawOf ν p θ₀` are `ν`-integrals weighted by the density. -/
private theorem integral_lawOf {Θ : Type*} {ν : Measure 𝓧} {p : Θ → 𝓧 → ℝ} {θ₀ : Θ}
    (hp_nonneg : ∀ x, 0 ≤ p θ₀ x) (hp_meas : Measurable (p θ₀)) (f : 𝓧 → ℝ) :
    ∫ x, f x ∂lawOf ν p θ₀ = ∫ x, p θ₀ x * f x ∂ν := by
  rw [lawOf, integral_withDensity_eq_integral_toReal_smul
    (f := fun x => ENNReal.ofReal (p θ₀ x)) hp_meas.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  congr 1; funext x
  rw [ENNReal.toReal_ofReal (hp_nonneg x), smul_eq_mul]

/-- Integrability under `lawOf ν p θ₀` is integrability of the density-weighted function. -/
private theorem integrable_lawOf_iff {Θ : Type*} {ν : Measure 𝓧} {p : Θ → 𝓧 → ℝ} {θ₀ : Θ}
    (hp_nonneg : ∀ x, 0 ≤ p θ₀ x) (hp_meas : Measurable (p θ₀)) (f : 𝓧 → ℝ) :
    Integrable f (lawOf ν p θ₀) ↔ Integrable (fun x => p θ₀ x * f x) ν := by
  rw [lawOf, integrable_withDensity_iff_integrable_smul'
    (f := fun x => ENNReal.ofReal (p θ₀ x)) hp_meas.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (hp_nonneg x), smul_eq_mul]

/-- For `p θ ≠ p θ₀` (not `ν`-a.e.), the expected log-likelihood ratio truncated below at `-2`
is negative: `log t ≤ 2 (√t - 1)` bounds it by minus the squared Hellinger distance. -/
private theorem integral_max_logRatio_neg {Θ : Type*} {ν : Measure 𝓧} {p : Θ → 𝓧 → ℝ} {θ₀ θ : Θ}
    (hp_pos : ∀ θ x, 0 < p θ x) (hp_meas : ∀ θ, Measurable (p θ))
    (hp_int : ∀ θ, ∫ x, p θ x ∂ν = 1) [IsFiniteMeasure (lawOf ν p θ₀)]
    {K : 𝓧 → ℝ} (hK : Integrable K (lawOf ν p θ₀))
    (hK_bound : ∀ θ x, Real.log (p θ x) - Real.log (p θ₀ x) ≤ K x)
    (hθ : ¬ p θ =ᵐ[ν] p θ₀) :
    ∫ x, max (Real.log (p θ x) - Real.log (p θ₀ x)) (-2) ∂lawOf ν p θ₀ < 0 := by
  have hpI : ∀ θ, Integrable (p θ) ν := fun θ => by
    by_contra h
    have := hp_int θ
    rw [integral_undef h] at this
    exact zero_ne_one this
  set f : 𝓧 → ℝ := fun x => max (Real.log (p θ x) - Real.log (p θ₀ x)) (-2)
  set u : 𝓧 → ℝ := fun x => Real.sqrt (p θ x)
  set v : 𝓧 → ℝ := fun x => Real.sqrt (p θ₀ x)
  have hu2 : ∀ x, u x ^ 2 = p θ x := fun x => Real.sq_sqrt (hp_pos θ x).le
  have hv2 : ∀ x, v x ^ 2 = p θ₀ x := fun x => Real.sq_sqrt (hp_pos θ₀ x).le
  have hf_meas : Measurable f :=
    (((hp_meas θ).log).sub (hp_meas θ₀).log).max measurable_const
  have hf_int : Integrable f (lawOf ν p θ₀) := by
    refine Integrable.mono' (hK.abs.add (integrable_const 2)) hf_meas.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have h1 := hK_bound θ x
    change ‖f x‖ ≤ |K x| + 2
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have : (-2 : ℝ) ≤ f x := le_max_right _ _
      linarith [abs_nonneg (K x)]
    · have : f x ≤ max (K x) (-2) := max_le_max h1 le_rfl
      have : max (K x) (-2) ≤ |K x| + 2 := max_le (by linarith [le_abs_self (K x)])
        (by linarith [abs_nonneg (K x)])
      linarith
  have hpf_int := (integrable_lawOf_iff (fun x => (hp_pos θ₀ x).le) (hp_meas θ₀) f).1 hf_int
  set w : 𝓧 → ℝ := fun x => (u x - v x) ^ 2
  have hw_meas : Measurable w :=
    ((Real.continuous_sqrt.measurable.comp (hp_meas θ)).sub
      (Real.continuous_sqrt.measurable.comp (hp_meas θ₀))).pow_const 2
  have hw_int : Integrable w ν := by
    refine Integrable.mono' (((hpI θ).add (hpI θ₀)).const_mul 2) hw_meas.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (u x - v x) ^ 2 ≤ 2 * (p θ x + p θ₀ x)
    rw [← hu2, ← hv2]; nlinarith [sq_nonneg (u x + v x)]
  -- pointwise Hellinger bound
  have hpt : ∀ x, p θ₀ x * f x ≤ p θ x - p θ₀ x - w x := fun x => by
    have hu : 0 < u x := Real.sqrt_pos.2 (hp_pos θ x)
    have hv : 0 < v x := Real.sqrt_pos.2 (hp_pos θ₀ x)
    have hlog : Real.log (p θ x) - Real.log (p θ₀ x) = 2 * Real.log (u x / v x) := by
      rw [Real.log_div hu.ne' hv.ne', ← hu2, ← hv2, Real.log_pow, Real.log_pow]; push_cast; ring
    have hle : f x ≤ 2 * (u x / v x - 1) := by
      apply max_le
      · rw [hlog]
        linarith [Real.log_le_sub_one_of_pos (div_pos hu hv)]
      · linarith [div_pos hu hv]
    calc p θ₀ x * f x ≤ p θ₀ x * (2 * (u x / v x - 1)) :=
          mul_le_mul_of_nonneg_left hle (hp_pos θ₀ x).le
      _ = p θ x - p θ₀ x - w x := by
          rw [← hu2, ← hv2]; simp only [w]; field_simp; ring
  have hw_pos : 0 < ∫ x, w x ∂ν := by
    rw [integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) hw_int]
    have hsupp : Function.support w = {x | ¬ p θ x = p θ₀ x} := by
      ext x
      simp only [Function.mem_support, Set.mem_ofPred_eq, w, ne_eq, pow_eq_zero_iff two_ne_zero,
        sub_eq_zero, u, v]
      rw [Real.sqrt_inj (hp_pos θ x).le (hp_pos θ₀ x).le]
    rw [hsupp, pos_iff_ne_zero]
    intro h0
    exact hθ (ae_iff.2 h0)
  rw [integral_lawOf (fun x => (hp_pos θ₀ x).le) (hp_meas θ₀)]
  calc ∫ x, p θ₀ x * f x ∂ν ≤ ∫ x, (p θ x - p θ₀ x - w x) ∂ν :=
        integral_mono hpf_int (((hpI θ).sub (hpI θ₀)).sub hw_int) hpt
    _ = - ∫ x, w x ∂ν := by
        have h12 : Integrable (fun x => p θ x - p θ₀ x) ν := (hpI θ).sub (hpI θ₀)
        rw [integral_sub h12 hw_int, integral_sub (hpI θ) (hpI θ₀),
          hp_int, hp_int]; ring
    _ < 0 := by linarith

/-- Around each `θ` with `p θ ≠ p θ₀`, the log-likelihood ratios on a small ball are bounded
by one measurable integrable function with negative mean (Wald's local step). -/
private theorem exists_local_envelope {Θ : Type*} [MetricSpace Θ]
    [TopologicalSpace.SeparableSpace Θ] {ν : Measure 𝓧} {p : Θ → 𝓧 → ℝ} {θ₀ θ : Θ}
    (hp_pos : ∀ θ x, 0 < p θ x) (hp_meas : ∀ θ, Measurable (p θ))
    (hp_cont : ∀ x, Continuous fun θ => p θ x)
    (hp_int : ∀ θ, ∫ x, p θ x ∂ν = 1) [IsFiniteMeasure (lawOf ν p θ₀)]
    {K : 𝓧 → ℝ} (hK : Integrable K (lawOf ν p θ₀))
    (hK_bound : ∀ θ x, Real.log (p θ x) - Real.log (p θ₀ x) ≤ K x)
    (hθ : ¬ p θ =ᵐ[ν] p θ₀) :
    ∃ r > 0, ∃ Z : 𝓧 → ℝ, Measurable Z ∧ Integrable Z (lawOf ν p θ₀) ∧
      ∫ x, Z x ∂lawOf ν p θ₀ < 0 ∧
      ∀ θ' ∈ Metric.ball θ r, ∀ x, Real.log (p θ' x) - Real.log (p θ₀ x) ≤ Z x := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense Θ
  set L : Θ → 𝓧 → ℝ := fun θ x => Real.log (p θ x) - Real.log (p θ₀ x)
  have hLc : ∀ x, Continuous fun θ => L θ x := fun x =>
    ((hp_cont x).log fun θ => (hp_pos θ x).ne').sub continuous_const
  have hLm : ∀ θ, Measurable (L θ) := fun θ => ((hp_meas θ).log).sub (hp_meas θ₀).log
  set S : ℝ → 𝓧 → ℝ := fun r x => ⨆ d : ↥(Metric.ball θ r ∩ D), L d x
  have hne : ∀ r, 0 < r → Nonempty ↥(Metric.ball θ r ∩ D) := fun r hr =>
    (hD.inter_open_nonempty _ Metric.isOpen_ball ⟨θ, Metric.mem_ball_self hr⟩).to_subtype
  have hbdd : ∀ r x, BddAbove (Set.range fun d : ↥(Metric.ball θ r ∩ D) => L d x) :=
    fun r x => ⟨K x, by rintro _ ⟨d, rfl⟩; exact hK_bound d x⟩
  have hS_le_K : ∀ r, 0 < r → ∀ x, S r x ≤ K x := fun r hr x => by
    have := hne r hr
    exact ciSup_le fun d => hK_bound d x
  have hS_ge : ∀ r x, ∀ θ' ∈ Metric.ball θ r, L θ' x ≤ S r x := fun r x θ' hθ' => by
    have hcl := hD.open_subset_closure_inter Metric.isOpen_ball hθ'
    have : closure (Metric.ball θ r ∩ D) ⊆ {θ'' | L θ'' x ≤ S r x} :=
      closure_minimal (fun d hd => le_ciSup (hbdd r x) ⟨d, hd⟩)
        (isClosed_le (hLc x) continuous_const)
    exact this hcl
  have hS_meas : ∀ r, Measurable (S r) := fun r => by
    have : Countable ↥(Metric.ball θ r ∩ D) := (hDc.mono Set.inter_subset_right).to_subtype
    exact Measurable.iSup fun d => hLm d
  set Z : ℝ → 𝓧 → ℝ := fun r x => max (S r x) (-2)
  have hZ_meas : ∀ r, Measurable (Z r) := fun r => (hS_meas r).max measurable_const
  have hZ_bound : ∀ r, 0 < r → ∀ x, ‖Z r x‖ ≤ |K x| + 2 := fun r hr x => by
    rw [Real.norm_eq_abs, abs_le]
    have h1 := hS_le_K r hr x
    constructor
    · have : (-2 : ℝ) ≤ Z r x := le_max_right _ _
      linarith [abs_nonneg (K x)]
    · have : Z r x ≤ max (K x) (-2) := max_le_max h1 le_rfl
      have : max (K x) (-2) ≤ |K x| + 2 := max_le (by linarith [le_abs_self (K x)])
        (by linarith [abs_nonneg (K x)])
      linarith
  have hB : Integrable (fun x => |K x| + 2) (lawOf ν p θ₀) := hK.abs.add (integrable_const 2)
  have hZ_int : ∀ r, 0 < r → Integrable (Z r) (lawOf ν p θ₀) := fun r hr =>
    Integrable.mono' hB (hZ_meas r).aestronglyMeasurable (Eventually.of_forall (hZ_bound r hr))
  set rs : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hrs : ∀ m, 0 < rs m := fun m => by positivity
  -- pointwise convergence of the envelopes
  have hlim : ∀ x, Tendsto (fun m => Z (rs m) x) atTop (𝓝 (max (L θ x) (-2))) := fun x => by
    refine Tendsto.max ?_ tendsto_const_nhds
    rw [tendsto_order]
    constructor
    · intro a ha
      exact Eventually.of_forall fun m =>
        lt_of_lt_of_le ha (hS_ge _ x θ (Metric.mem_ball_self (hrs m)))
    · intro a ha
      obtain ⟨δ, hδ, hδL⟩ := Metric.continuous_iff.1 (hLc x) θ ((a - L θ x) / 2) (by linarith)
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
      refine eventually_atTop.2 ⟨N, fun m hm => ?_⟩
      have := hne (rs m) (hrs m)
      have hrm : rs m ≤ 1 / ((N : ℝ) + 1) := by
        simp only [rs]
        gcongr
      refine lt_of_le_of_lt (ciSup_le fun d => ?_) (by linarith : L θ x + (a - L θ x) / 2 < a)
      have hd : dist (d : Θ) θ < δ :=
        lt_of_lt_of_le (Metric.mem_ball.1 d.2.1) (hrm.trans hN.le)
      have := hδL d hd
      rw [Real.dist_eq, abs_lt] at this
      linarith
  have hconv : Tendsto (fun m => ∫ x, Z (rs m) x ∂lawOf ν p θ₀) atTop
      (𝓝 (∫ x, max (L θ x) (-2) ∂lawOf ν p θ₀)) :=
    tendsto_integral_of_dominated_convergence (fun x => |K x| + 2)
      (fun m => (hZ_meas _).aestronglyMeasurable) hB
      (fun m => Eventually.of_forall (hZ_bound _ (hrs m))) (Eventually.of_forall hlim)
  have hneg := integral_max_logRatio_neg hp_pos hp_meas hp_int hK hK_bound hθ
  obtain ⟨m, hm⟩ := (hconv.eventually (gt_mem_nhds hneg)).exists
  exact ⟨rs m, hrs m, Z (rs m), hZ_meas _, hZ_int _ (hrs m), hm,
    fun θ' hθ' x => (hS_ge _ x θ' hθ').trans (le_max_left _ _)⟩

/-- Compactness: finitely many such envelopes cover the parameters at distance `≥ ε` from `θ₀`.
-/
private theorem exists_finite_envelopes {Θ : Type*} [MetricSpace Θ] [CompactSpace Θ]
    {ν : Measure 𝓧} {p : Θ → 𝓧 → ℝ} {θ₀ : Θ}
    (hp_pos : ∀ θ x, 0 < p θ x) (hp_meas : ∀ θ, Measurable (p θ))
    (hp_cont : ∀ x, Continuous fun θ => p θ x)
    (hp_int : ∀ θ, ∫ x, p θ x ∂ν = 1) (hident : ∀ θ, p θ =ᵐ[ν] p θ₀ → θ = θ₀)
    [IsFiniteMeasure (lawOf ν p θ₀)]
    {K : 𝓧 → ℝ} (hK : Integrable K (lawOf ν p θ₀))
    (hK_bound : ∀ θ x, Real.log (p θ x) - Real.log (p θ₀ x) ≤ K x) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Finset Θ, ∃ Z : Θ → 𝓧 → ℝ,
      (∀ θ ∈ t, Measurable (Z θ) ∧ Integrable (Z θ) (lawOf ν p θ₀) ∧
        ∫ x, Z θ x ∂lawOf ν p θ₀ < 0) ∧
      ∀ θ, ε ≤ dist θ θ₀ → ∃ θ' ∈ t, ∀ x,
        Real.log (p θ x) - Real.log (p θ₀ x) ≤ Z θ' x := by
  classical
  set F : Set Θ := {θ | ε ≤ dist θ θ₀}
  have hF : IsCompact F :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).isCompact
  have hne : ∀ θ ∈ F, ¬ p θ =ᵐ[ν] p θ₀ := fun θ hθ h => by
    have := hident θ h
    subst this
    simp [F] at hθ
    linarith
  choose r hr Z hZm hZi hZneg hZle using fun θ (hθ : θ ∈ F) =>
    exists_local_envelope hp_pos hp_meas hp_cont hp_int hK hK_bound (hne θ hθ)
  set U : Θ → Set Θ := fun θ => if h : θ ∈ F then Metric.ball θ (r θ h) else Set.univ
  have hU : ∀ θ ∈ F, U θ ∈ 𝓝 θ := fun θ hθ => by
    simp only [U, hθ, ↓reduceDIte]
    exact Metric.ball_mem_nhds θ (hr θ hθ)
  obtain ⟨t, htF, hcov⟩ := hF.elim_nhds_subcover U hU
  refine ⟨t, fun θ x => if h : θ ∈ F then Z θ h x else 0, fun θ hθ => ?_, fun θ hθ => ?_⟩
  · have h := htF θ hθ
    simp only [h, ↓reduceDIte]
    exact ⟨hZm θ h, hZi θ h, hZneg θ h⟩
  · obtain ⟨θ', hθ't, hθU⟩ := Set.mem_iUnion₂.1 (hcov hθ)
    have h := htF θ' hθ't
    refine ⟨θ', hθ't, fun x => ?_⟩
    simp only [U, h, ↓reduceDIte] at hθU
    simp only [h, ↓reduceDIte]
    exact hZle θ' h θ hθU x

/-- The strong law of large numbers for `Z (X i)`. -/
private theorem ae_tendsto_average {Θ : Type*} {ν : Measure 𝓧} {p : Θ → 𝓧 → ℝ} {θ₀ : Θ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → 𝓧}
    (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    {Z : 𝓧 → ℝ} (hZ : Measurable Z) (hZi : Integrable Z (lawOf ν p θ₀)) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, Z (X i ω)) / n) atTop
      (𝓝 (∫ x, Z x ∂lawOf ν p θ₀)) := by
  have hident : ∀ i, IdentDistrib (Z ∘ X i) (Z ∘ X 0) P P := fun i =>
    (⟨(hX_law i).aemeasurable, (hX_law 0).aemeasurable,
      (hX_law i).map_eq.trans (hX_law 0).map_eq.symm⟩ : IdentDistrib (X i) (X 0) P P).comp hZ
  have h := strong_law_ae_real (fun i => Z ∘ X i) ((hX_law 0).integrable_comp hZi)
    (fun i j hij => (hX_indep.comp (fun _ => Z) (fun _ => hZ)).indepFun hij) hident
  rwa [(hX_law 0).integral_comp hZ.aestronglyMeasurable] at h

/-- **Wald's consistency theorem for maximum likelihood** (Ferguson's form, positive
densities). Let `Θ` be a compact metric space and `p θ` probability densities with respect to
`ν`, positive, measurable in `x` and continuous in `θ`. Assume the model is identifiable
(`p θ = p θ₀` `ν`-a.e. only for `θ = θ₀`) and that the log-likelihood ratios have an upper
envelope `K` integrable under `p θ₀`. Let `X 0, X 1, …` be independent with law `p θ₀ ν`, and
let `θhat n ω` maximize the log-likelihood `∑_{i<n} log p θ (X i ω)` over `θ ∈ Θ`. Then
`θhat n → θ₀` almost surely.

Source: Wald (1949); Ferguson (1996), Theorem 17.
Proves the deferred entry `ae_tendsto_maximumLikelihood`. -/
theorem ae_tendsto_maximumLikelihood {Θ : Type*} [MetricSpace Θ] [CompactSpace Θ]
    {ν : Measure 𝓧} {p : Θ → 𝓧 → ℝ} {θ₀ : Θ}
    (hp_pos : ∀ θ x, 0 < p θ x) (hp_meas : ∀ θ, Measurable (p θ))
    (hp_cont : ∀ x, Continuous fun θ => p θ x) (hp_int : ∀ θ, ∫ x, p θ x ∂ν = 1)
    (hident : ∀ θ, p θ =ᵐ[ν] p θ₀ → θ = θ₀)
    {K : 𝓧 → ℝ} (hK : Integrable K (lawOf ν p θ₀))
    (hK_bound : ∀ θ x, Real.log (p θ x) - Real.log (p θ₀ x) ≤ K x)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → 𝓧}
    (hX_law : ∀ i, HasLaw (X i) (lawOf ν p θ₀) P) (hX_indep : iIndepFun X P)
    {θhat : ℕ → Ω → Θ}
    (hmle : ∀ n ω θ, ∑ i ∈ Finset.range n, Real.log (p θ (X i ω)) ≤
      ∑ i ∈ Finset.range n, Real.log (p (θhat n ω) (X i ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun n => θhat n ω) atTop (𝓝 θ₀) := by
  have : IsProbabilityMeasure (lawOf ν p θ₀) :=
    (hX_law 0).isProbabilityMeasure_iff.1 inferInstance
  have hε : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  choose t Z hZ hcov using fun k : ℕ =>
    exists_finite_envelopes hp_pos hp_meas hp_cont hp_int hident hK hK_bound (hε k)
  have hgood : ∀ᵐ ω ∂P, ∀ k, ∀ θ ∈ t k, Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range n, Z k θ (X i ω)) / n) atTop
      (𝓝 (∫ x, Z k θ x ∂lawOf ν p θ₀)) := by
    rw [ae_all_iff]
    intro k
    rw [eventually_all_finset]
    intro θ hθ
    exact ae_tendsto_average hX_law hX_indep (hZ k θ hθ).1 (hZ k θ hθ).2.1
  filter_upwards [hgood] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε0
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε0
  have hev : ∀ᶠ n : ℕ in atTop, ∀ θ ∈ t k,
      (∑ i ∈ Finset.range n, Z k θ (X i ω)) / n < 0 := by
    rw [eventually_all_finset]
    intro θ hθ
    exact (hω k θ hθ).eventually (gt_mem_nhds (hZ k θ hθ).2.2)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  by_contra hfar
  replace hfar := not_lt.1 hfar
  obtain ⟨θ', hθ't, hle⟩ := hcov k (θhat n ω) (hk.le.trans hfar)
  have h0 : 0 ≤ ∑ i ∈ Finset.range n,
      (Real.log (p (θhat n ω) (X i ω)) - Real.log (p θ₀ (X i ω))) := by
    rw [Finset.sum_sub_distrib]; linarith [hmle n ω θ₀]
  have h1 : 0 ≤ ∑ i ∈ Finset.range n, Z k θ' (X i ω) :=
    h0.trans (Finset.sum_le_sum fun i _ => hle (X i ω))
  have h2 := hN n hn θ' hθ't
  have : 0 ≤ (∑ i ∈ Finset.range n, Z k θ' (X i ω)) / n := div_nonneg h1 (Nat.cast_nonneg n)
  linarith

end MathlibExt.Probability.Statistics.FisherInformation
