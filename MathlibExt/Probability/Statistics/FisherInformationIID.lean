/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Pi
public import MathlibExt.Probability.Statistics.FisherInformation
public import MathlibExt.Probability.Statistics.MLEAsymptoticNormality

/-!
# Fisher information adds over iid observations

For a one-parameter family with per-observation information `I(θ)`, the joint n-sample
family (product dominating measure, product density) has information `n • I(θ)`. The
score mean-zero interface `hmean` is discharged at integration by L7-14
`integral_score_mean_zero`, whose conclusion is byte-identical to the interface up to
the renaming `θ₀ ↦ θ`.

## References

* H. Cramér, *Mathematical Methods of Statistics* (1946), ch. 32.
* C. R. Rao, "Information and the accuracy attainable in the estimation of statistical
  parameters", Bull. Calcutta Math. Soc. 37 (1945) 81–91.
* E. L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed. (1998), ch. 2.

Source: iid additivity is the finite-product score computation from that
Fisher-information/score framework (joint score = sum of per-observation scores;
diagonal second moments give `I(θ)`; cross terms vanish by independence at mean-zero
score). This Lean proof adds the `hS_int`/`hS2_int` regularity hypotheses (score and
score-squared integrability), which the textbook computation takes for granted. The
closely adapted formal context is exactly the imported Atlas declarations
`FisherInformation.fisherInformation`/`lawOf` and
`MLEAsymptoticNormality.score`/`integral_score_sq`; no external formalization was
adapted.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.FisherInformation

open MeasureTheory Filter Topology MathlibExt.Probability.Statistics.MLEAsymptoticNormality

-- Private helpers for `fisherInformation_iid` (approach: rewrite the joint information via
-- `integral_score_sq`, expand the squared joint score, and evaluate each pair integral by
-- reducing the joint law to the product base measure and factorizing over `Measure.pi`).

/-- The dominating measure is σ-finite: `ν = lawOf.withDensity (ofReal p)⁻¹` with a
finite-everywhere density, and the law is σ-finite as a probability measure. -/
private theorem sigmaFinite_of_lawOf {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ : ℝ}
    (hp_pos : ∀ x, 0 < p θ x) (hp_meas : Measurable (p θ))
    (hnorm : IsProbabilityMeasure (lawOf ν p θ)) :
    SigmaFinite ν := by
  have := hnorm
  have hmeas : Measurable (fun x => ENNReal.ofReal (p θ x)) := hp_meas.ennreal_ofReal
  have hne0 : ∀ᵐ x ∂ν, (ENNReal.ofReal (p θ x)) ≠ 0 :=
    Filter.Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (hp_pos x)).ne'
  have hnetop : ∀ᵐ x ∂ν, (ENNReal.ofReal (p θ x)) ≠ ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top.ne
  have hν : ν = (lawOf ν p θ).withDensity (fun x => (ENNReal.ofReal (p θ x))⁻¹) := by
    have h := MeasureTheory.withDensity_inv_same (μ := ν)
      (f := fun x => ENNReal.ofReal (p θ x)) hmeas hne0 hnetop
    change ν = (ν.withDensity fun x => ENNReal.ofReal (p θ x)).withDensity _
    exact h.symm
  rw [hν]
  exact MeasureTheory.SigmaFinite.withDensity_of_ne_top' fun x hcon =>
    (ENNReal.ofReal_pos.mpr (hp_pos x)).ne' (ENNReal.inv_eq_top.mp hcon)

/-- The single-observation density is integrable against `ν`. -/
private theorem integrable_density {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ : ℝ}
    (hp_pos : ∀ x, 0 < p θ x) (hp_meas : Measurable (p θ))
    (hnorm : IsProbabilityMeasure (lawOf ν p θ)) :
    Integrable (p θ) ν := by
  have := hnorm
  have h1 : Integrable (fun _ : 𝓧 => (1 : ℝ)) (lawOf ν p θ) := integrable_const 1
  have h1' : Integrable (fun _ : 𝓧 => (1 : ℝ))
      (ν.withDensity fun x => ENNReal.ofReal (p θ x)) := h1
  have h2 : Integrable (fun x => (ENNReal.ofReal (p θ x)).toReal • (1 : ℝ)) ν :=
    (MeasureTheory.integrable_withDensity_iff_integrable_smul' (μ := ν)
      (f := fun x => ENNReal.ofReal (p θ x)) hp_meas.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp h1'
  have h3 : (fun x => (ENNReal.ofReal (p θ x)).toReal • (1 : ℝ)) = p θ := by
    funext x
    rw [ENNReal.toReal_ofReal (le_of_lt (hp_pos x)), smul_eq_mul, mul_one]
  rw [h3] at h2
  exact h2

/-- The single-observation density integrates to one (normalization). -/
private theorem integral_density_eq_one {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ : ℝ}
    (hp_pos : ∀ x, 0 < p θ x) (hp_meas : Measurable (p θ))
    (hnorm : IsProbabilityMeasure (lawOf ν p θ)) :
    ∫ x, p θ x ∂ν = 1 := by
  have := hnorm
  have h_nonneg : 0 ≤ᵐ[ν] (p θ) :=
    Filter.Eventually.of_forall fun x => le_of_lt (hp_pos x)
  have h_aesm : AEStronglyMeasurable (p θ) ν := hp_meas.aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae h_nonneg h_aesm]
  have hmass : ∫⁻ x, ENNReal.ofReal (p θ x) ∂ν = 1 := by
    have h1 : (lawOf ν p θ) Set.univ = 1 := measure_univ
    have hwd : (lawOf ν p θ) Set.univ = ∫⁻ x, ENNReal.ofReal (p θ x) ∂ν := by
      have h : (ν.withDensity fun x => ENNReal.ofReal (p θ x)) Set.univ
          = ∫⁻ x, ENNReal.ofReal (p θ x) ∂ν := by
        rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
      exact h
    rw [← hwd]
    exact h1
  rw [hmass, ENNReal.toReal_one]

/-- `score * density` is integrable against `ν` (from `hS_int` via the density). -/
private theorem integrable_score_mul_density {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ : ℝ}
    (hp_pos : ∀ x, 0 < p θ x) (hp_meas : Measurable (p θ))
    (hS_int : Integrable (score p θ) (lawOf ν p θ)) :
    Integrable (fun y => score p θ y * p θ y) ν := by
  have h1' : Integrable (score p θ)
      (ν.withDensity fun x => ENNReal.ofReal (p θ x)) := hS_int
  have h2 : Integrable (fun x => (ENNReal.ofReal (p θ x)).toReal • score p θ x) ν :=
    (MeasureTheory.integrable_withDensity_iff_integrable_smul' (μ := ν)
      (f := fun x => ENNReal.ofReal (p θ x)) hp_meas.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp h1'
  have h3 : (fun x => (ENNReal.ofReal (p θ x)).toReal • score p θ x)
      = fun y => score p θ y * p θ y := by
    funext x
    rw [ENNReal.toReal_ofReal (le_of_lt (hp_pos x)), smul_eq_mul, mul_comm]
  rw [h3] at h2
  exact h2

/-- `∫ score * density = 0` (from `hmean` via the density). -/
private theorem integral_score_mul_density {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ : ℝ}
    (hp_pos : ∀ x, 0 < p θ x) (hp_meas : Measurable (p θ))
    (hmean : ∫ x, score p θ x ∂lawOf ν p θ = 0) :
    ∫ y, score p θ y * p θ y ∂ν = 0 := by
  have hmean' : ∫ x, score p θ x ∂(ν.withDensity fun x => ENNReal.ofReal (p θ x)) = 0 :=
    hmean
  have h := integral_withDensity_eq_integral_toReal_smul (μ := ν)
    (f := fun x => ENNReal.ofReal (p θ x)) hp_meas.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)
    (score p θ)
  rw [h] at hmean'
  have h3 : (fun x => (ENNReal.ofReal (p θ x)).toReal • score p θ x)
      = fun y => score p θ y * p θ y := by
    funext x
    rw [ENNReal.toReal_ofReal (le_of_lt (hp_pos x)), smul_eq_mul, mul_comm]
  rw [h3] at hmean'
  exact hmean'

/-- `score² * density` is integrable against `ν` (from `hS2_int` via the density). -/
private theorem integrable_score_sq_mul_density {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ : ℝ}
    (hp_pos : ∀ x, 0 < p θ x) (hp_meas : Measurable (p θ))
    (hS2_int : Integrable (fun x => (score p θ x) ^ 2) (lawOf ν p θ)) :
    Integrable (fun y => (score p θ y) ^ 2 * p θ y) ν := by
  have h1' : Integrable (fun x => (score p θ x) ^ 2)
      (ν.withDensity fun x => ENNReal.ofReal (p θ x)) := hS2_int
  have h2 : Integrable (fun x => (ENNReal.ofReal (p θ x)).toReal • (score p θ x) ^ 2) ν :=
    (MeasureTheory.integrable_withDensity_iff_integrable_smul' (μ := ν)
      (f := fun x => ENNReal.ofReal (p θ x)) hp_meas.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp h1'
  have h3 : (fun x => (ENNReal.ofReal (p θ x)).toReal • (score p θ x) ^ 2)
      = fun y => (score p θ y) ^ 2 * p θ y := by
    funext x
    rw [ENNReal.toReal_ofReal (le_of_lt (hp_pos x)), smul_eq_mul, mul_comm]
  rw [h3] at h2
  exact h2

/-- `∫ score² * density = I(θ)` (from `integral_score_sq` via the density). -/
private theorem integral_score_sq_mul_density {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ : ℝ}
    (hp_pos : ∀ x, 0 < p θ x) (hp_meas : Measurable (p θ))
    (hp_diff : ∀ x, DifferentiableAt ℝ (fun t => p t x) θ) :
    ∫ y, (score p θ y) ^ 2 * p θ y ∂ν = fisherInformation ν p θ := by
  have hSq := integral_score_sq (ν := ν) hp_pos hp_meas hp_diff
  have hSq' : ∫ x, (score p θ x) ^ 2
      ∂(ν.withDensity fun x => ENNReal.ofReal (p θ x)) = fisherInformation ν p θ := hSq
  have h := integral_withDensity_eq_integral_toReal_smul (μ := ν)
    (f := fun x => ENNReal.ofReal (p θ x)) hp_meas.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)
    (fun x => (score p θ x) ^ 2)
  rw [h] at hSq'
  have h3 : (fun x => (ENNReal.ofReal (p θ x)).toReal • (score p θ x) ^ 2)
      = fun y => (score p θ y) ^ 2 * p θ y := by
    funext x
    rw [ENNReal.toReal_ofReal (le_of_lt (hp_pos x)), smul_eq_mul, mul_comm]
  rw [h3] at hSq'
  exact hSq'

/-- The joint density is positive. -/
private theorem joint_pos (n : ℕ) {𝓧 : Type*} [MeasurableSpace 𝓧]
    {p : ℝ → 𝓧 → ℝ} {θ : ℝ}
    (hp_pos : ∀ x, 0 < p θ x) (x : Fin n → 𝓧) :
    0 < ∏ i, p θ (x i) :=
  Finset.prod_pos fun i _ => hp_pos (x i)

/-- The joint density is measurable. -/
private theorem joint_meas (n : ℕ) {𝓧 : Type*} [MeasurableSpace 𝓧]
    {p : ℝ → 𝓧 → ℝ} {θ : ℝ}
    (hp_meas : Measurable (p θ)) :
    Measurable (fun x : Fin n → 𝓧 => ∏ i, p θ (x i)) :=
  Finset.measurable_prod _ fun i _ => hp_meas.comp (measurable_pi_apply i)

/-- The joint density is differentiable in `θ`. -/
private theorem joint_diff (n : ℕ) {𝓧 : Type*} [MeasurableSpace 𝓧]
    {p : ℝ → 𝓧 → ℝ} {θ : ℝ}
    (hp_diff : ∀ x, DifferentiableAt ℝ (fun t => p t x) θ) (x : Fin n → 𝓧) :
    DifferentiableAt ℝ (fun t => ∏ i, p t (x i)) θ := by
  have h2 := DifferentiableAt.finsetProd (u := (Finset.univ : Finset (Fin n)))
    (f := fun i t => p t (x i)) (fun i _ => hp_diff (x i))
  have hfun : (fun t => ∏ i, p t (x i)) = (∏ i, fun t => p t (x i)) := by
    funext t
    show (∏ i, p t (x i)) = _
    rw [Finset.prod_apply]
  rw [hfun]
  exact h2

/-- The joint score is the sum of the per-observation scores. -/
private theorem joint_score_eq_sum (n : ℕ) {𝓧 : Type*} [MeasurableSpace 𝓧]
    {p : ℝ → 𝓧 → ℝ} {θ : ℝ}
    (hp_pos : ∀ x, 0 < p θ x)
    (hp_diff : ∀ x, DifferentiableAt ℝ (fun t => p t x) θ) (x : Fin n → 𝓧) :
    score (fun θ' x => ∏ i, p θ' (x i)) θ x
      = ∑ i, score p θ (x i) := by
  have hev : ∀ᶠ t in 𝓝 θ, ∀ i, 0 < p t (x i) := by
    rw [Filter.eventually_all]
    intro i
    exact Tendsto.eventually_const_lt (hp_pos (x i)) (hp_diff (x i)).continuousAt
  have heq : (fun t => Real.log (∏ i, p t (x i)))
      =ᶠ[𝓝 θ] (fun t => ∑ i, Real.log (p t (x i))) :=
    hev.mono fun t ht => Real.log_prod (fun i _ => (ht i).ne')
  have hderiv := Filter.EventuallyEq.deriv_eq heq
  have hsum : deriv (fun t => ∑ i, Real.log (p t (x i))) θ
      = ∑ i, deriv (fun t => Real.log (p t (x i))) θ := by
    have h := deriv_sum (u := (Finset.univ : Finset (Fin n)))
      (A := fun i t => Real.log (p t (x i))) (x := θ)
      (fun i _ => ((hp_diff (x i)).log (hp_pos (x i)).ne'))
    have hfun : (fun t => ∑ i, Real.log (p t (x i)))
        = (∑ i, fun t => Real.log (p t (x i))) := by
      funext t
      show (∑ i, Real.log (p t (x i))) = _
      rw [Finset.sum_apply]
    rw [hfun]
    exact h
  change deriv (fun t => Real.log (∏ i, p t (x i))) θ = ∑ i, score p θ (x i)
  rw [hderiv, hsum]
  rfl

/-- Per-coordinate factor for the `(i, j)` pair integrand over the product base measure:
at coordinate `k` it contributes the score when `k` is one of the pair indices and `1`
otherwise, times the single-observation density. -/
private noncomputable def crossFactor {𝓧 : Type*} [MeasurableSpace 𝓧]
    (p : ℝ → 𝓧 → ℝ) (θ : ℝ) (n : ℕ) (i j k : Fin n) (y : 𝓧) : ℝ :=
  (if k = i then score p θ y else 1) * (if k = j then score p θ y else 1) * p θ y

/-- Each per-coordinate factor is integrable against `ν`. -/
private theorem factor_int {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ : ℝ} (n : ℕ)
    (hp_pos : ∀ x, 0 < p θ x) (hp_meas : Measurable (p θ))
    (hnorm : IsProbabilityMeasure (lawOf ν p θ))
    (hS_int : Integrable (score p θ) (lawOf ν p θ))
    (hS2_int : Integrable (fun x => (score p θ x) ^ 2) (lawOf ν p θ))
    (i j k : Fin n) :
    Integrable (fun y => crossFactor p θ n i j k y) ν := by
  have hP := integrable_density hp_pos hp_meas hnorm
  have hSP := integrable_score_mul_density hp_pos hp_meas hS_int
  have hS2P := integrable_score_sq_mul_density hp_pos hp_meas hS2_int
  by_cases hki : k = i <;> by_cases hkj : k = j
  · have heq : (fun y => crossFactor p θ n i j k y)
        = fun y => (score p θ y) ^ 2 * p θ y := by
      funext y
      change (if k = i then score p θ y else 1) * (if k = j then score p θ y else 1)
        * p θ y = _
      simp only [ite_eq_left hki, ite_eq_left hkj]
      ring
    rw [heq]
    exact hS2P
  · have heq : (fun y => crossFactor p θ n i j k y)
        = fun y => score p θ y * p θ y := by
      funext y
      change (if k = i then score p θ y else 1) * (if k = j then score p θ y else 1)
        * p θ y = _
      simp only [ite_eq_left hki, ite_eq_right hkj]
      ring
    rw [heq]
    exact hSP
  · have heq : (fun y => crossFactor p θ n i j k y)
        = fun y => score p θ y * p θ y := by
      funext y
      change (if k = i then score p θ y else 1) * (if k = j then score p θ y else 1)
        * p θ y = _
      simp only [ite_eq_right hki, ite_eq_left hkj]
      ring
    rw [heq]
    exact hSP
  · have heq : (fun y => crossFactor p θ n i j k y) = p θ := by
      funext y
      change (if k = i then score p θ y else 1) * (if k = j then score p θ y else 1)
        * p θ y = _
      simp only [ite_eq_right hki, ite_eq_right hkj]
      ring
    rw [heq]
    exact hP

/-- Off-pair factor integral: `∫ p = 1`. -/
private theorem factor_val_off {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ : ℝ} (n : ℕ)
    (hp_pos : ∀ x, 0 < p θ x) (hp_meas : Measurable (p θ))
    (hnorm : IsProbabilityMeasure (lawOf ν p θ))
    (i j k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) :
    ∫ y, crossFactor p θ n i j k y ∂ν = 1 := by
  have hP := integral_density_eq_one hp_pos hp_meas hnorm
  have heq : (fun y => crossFactor p θ n i j k y) = p θ := by
    funext y
    change (if k = i then score p θ y else 1) * (if k = j then score p θ y else 1)
      * p θ y = _
    simp only [ite_eq_right hki, ite_eq_right hkj]
    ring
  rw [heq]
  exact hP

/-- Diagonal factor integral: `∫ score² * p = I(θ)`. -/
private theorem factor_val_diag {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ : ℝ} (n : ℕ)
    (hp_pos : ∀ x, 0 < p θ x) (hp_meas : Measurable (p θ))
    (hp_diff : ∀ x, DifferentiableAt ℝ (fun t => p t x) θ)
    (i k : Fin n) (hki : k = i) :
    ∫ y, crossFactor p θ n i i k y ∂ν = fisherInformation ν p θ := by
  have hS2P := integral_score_sq_mul_density (ν := ν) hp_pos hp_meas hp_diff
  have heq : (fun y => crossFactor p θ n i i k y)
      = fun y => (score p θ y) ^ 2 * p θ y := by
    funext y
    change (if k = i then score p θ y else 1) * (if k = i then score p θ y else 1)
      * p θ y = _
    simp only [ite_eq_left hki]
    ring
  rw [heq]
  exact hS2P

/-- Cross factor integral at the pair index: `∫ score * p = 0`. -/
private theorem factor_val_cross {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ : ℝ} (n : ℕ)
    (hp_pos : ∀ x, 0 < p θ x) (hp_meas : Measurable (p θ))
    (hmean : ∫ x, score p θ x ∂lawOf ν p θ = 0)
    (i j : Fin n) (hij : i ≠ j) :
    ∫ y, crossFactor p θ n i j i y ∂ν = 0 := by
  have hSP := integral_score_mul_density hp_pos hp_meas hmean
  have heq : (fun y => crossFactor p θ n i j i y)
      = fun y => score p θ y * p θ y := by
    funext y
    change (if i = i then score p θ y else 1) * (if i = j then score p θ y else 1)
      * p θ y = _
    simp only [ite_true, ite_eq_right hij]
    ring
  rw [heq]
  exact hSP

/-- The joint-law pair integrand, pushed to the product base measure, is the product of
the per-coordinate factors. -/
private theorem integrand_eq_factor_prod {𝓧 : Type*} [MeasurableSpace 𝓧]
    {p : ℝ → 𝓧 → ℝ} {θ : ℝ} (n : ℕ)
    (hp_pos : ∀ x, 0 < p θ x) (i j : Fin n) (x : Fin n → 𝓧) :
    (ENNReal.ofReal (∏ k, p θ (x k))).toReal • (score p θ (x i) * score p θ (x j))
      = ∏ k, crossFactor p θ n i j k (x k) := by
  have h1 : (∏ k, crossFactor p θ n i j k (x k))
      = (∏ k, (if k = i then score p θ (x k) else 1))
        * (∏ k, (if k = j then score p θ (x k) else 1))
        * (∏ k, p θ (x k)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => rfl
  rw [h1]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  rw [ENNReal.toReal_ofReal (le_of_lt (joint_pos n hp_pos x)), smul_eq_mul]
  ring

/-- **Fisher information adds over iid observations.** The joint n-sample information is
`n` times the single-observation information. The score mean-zero interface is discharged
at integration by `integral_score_mean_zero` (L7-14).
Source: Cramér (1946), ch. 32; Rao (1945); Lehmann & Casella (1998), ch. 2; see the
module References. The `hS_int`/`hS2_int` hypotheses are this formalization's added
regularity. -/
theorem fisherInformation_iid (n : ℕ) {𝓧 : Type*} [MeasurableSpace 𝓧]
    {ν : Measure 𝓧} {p : ℝ → 𝓧 → ℝ} {θ : ℝ}
    (hp_pos : ∀ x, 0 < p θ x) (hp_meas : Measurable (p θ))
    (hp_diff : ∀ x, DifferentiableAt ℝ (fun t => p t x) θ)
    (hnorm : IsProbabilityMeasure (lawOf ν p θ))
    (hmean : ∫ x, MathlibExt.Probability.Statistics.MLEAsymptoticNormality.score p θ x
      ∂lawOf ν p θ = 0)
    (hS_int : Integrable
      (MathlibExt.Probability.Statistics.MLEAsymptoticNormality.score p θ)
      (lawOf ν p θ))
    (hS2_int : Integrable
      (fun x => (MathlibExt.Probability.Statistics.MLEAsymptoticNormality.score p θ x) ^ 2)
      (lawOf ν p θ)) :
    fisherInformation (Measure.pi fun _ : Fin n => ν)
        (fun θ' x => ∏ i, p θ' (x i)) θ
      = n * fisherInformation ν p θ := by
  have hSFν : SigmaFinite ν := sigmaFinite_of_lawOf hp_pos hp_meas hnorm
  have hSFpi : ∀ i : Fin n, SigmaFinite ν := fun _ => hSFν
  have hJP : fisherInformation (Measure.pi fun _ : Fin n => ν)
        (fun θ' x => ∏ i, p θ' (x i)) θ
      = ∫ x, (score (fun θ' x => ∏ i, p θ' (x i)) θ x) ^ 2
        ∂(lawOf (Measure.pi fun _ : Fin n => ν) (fun θ' x => ∏ i, p θ' (x i)) θ) := by
    have h := integral_score_sq (ν := Measure.pi fun _ : Fin n => ν)
      (p := fun θ' x => ∏ i, p θ' (x i)) (θ := θ)
      (fun x => joint_pos n hp_pos x) (joint_meas n hp_meas)
      (fun x => joint_diff n hp_diff x)
    exact h.symm
  rw [hJP]
  have hsq : (fun x : Fin n → 𝓧 =>
        (score (fun θ' x => ∏ i, p θ' (x i)) θ x) ^ 2)
      = fun x => ∑ i, ∑ j, score p θ (x i) * score p θ (x j) := by
    funext x
    have hsx := joint_score_eq_sum n hp_pos hp_diff x
    rw [hsx, pow_two]
    exact Finset.sum_mul_sum _ _ _ _
  rw [hsq]
  have hint : ∀ i j, Integrable
      (fun x : Fin n → 𝓧 => score p θ (x i) * score p θ (x j))
      (lawOf (Measure.pi fun _ : Fin n => ν) (fun θ' x => ∏ i, p θ' (x i)) θ) := by
    intro i j
    apply (MeasureTheory.integrable_withDensity_iff_integrable_smul'
      (μ := Measure.pi fun _ : Fin n => ν)
      (f := fun x : Fin n → 𝓧 => ENNReal.ofReal (∏ k, p θ (x k)))
      ((joint_meas n hp_meas).ennreal_ofReal)
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)
      (g := fun x : Fin n → 𝓧 => score p θ (x i) * score p θ (x j))).mpr
    change Integrable (fun x : Fin n → 𝓧 => (ENNReal.ofReal (∏ k, p θ (x k))).toReal
      • (score p θ (x i) * score p θ (x j))) (Measure.pi fun _ : Fin n => ν)
    have hpt : (fun x : Fin n → 𝓧 => (ENNReal.ofReal (∏ k, p θ (x k))).toReal
          • (score p θ (x i) * score p θ (x j)))
        = fun x => ∏ k, crossFactor p θ n i j k (x k) :=
      funext fun x => integrand_eq_factor_prod n hp_pos i j x
    rw [hpt]
    exact MeasureTheory.Integrable.fintype_prod (μ := fun _ : Fin n => ν)
      (f := fun k (y : 𝓧) => crossFactor p θ n i j k y)
      (fun k => factor_int n hp_pos hp_meas hnorm hS_int hS2_int i j k)
  have hsplit_outer : (∫ x : Fin n → 𝓧, (∑ i, ∑ j, score p θ (x i) * score p θ (x j))
        ∂(lawOf (Measure.pi fun _ : Fin n => ν) (fun θ' x => ∏ i, p θ' (x i)) θ))
      = ∑ i, ∫ x : Fin n → 𝓧, (∑ j, score p θ (x i) * score p θ (x j))
        ∂(lawOf (Measure.pi fun _ : Fin n => ν) (fun θ' x => ∏ i, p θ' (x i)) θ) := by
    exact integral_finsetSum (G := ℝ) (s := (Finset.univ : Finset (Fin n)))
      (f := fun (i : Fin n) (x : Fin n → 𝓧) => ∑ j, score p θ (x i) * score p θ (x j))
      (fun i _ => integrable_finsetSum (s := (Finset.univ : Finset (Fin n)))
        (f := fun (j : Fin n) (x : Fin n → 𝓧) => score p θ (x i) * score p θ (x j))
        (fun j _ => hint i j))
  have hsplit_inner : ∀ i, (∫ x : Fin n → 𝓧,
        (∑ j, score p θ (x i) * score p θ (x j))
        ∂(lawOf (Measure.pi fun _ : Fin n => ν) (fun θ' x => ∏ i, p θ' (x i)) θ))
      = ∑ j, ∫ x : Fin n → 𝓧, (score p θ (x i) * score p θ (x j))
        ∂(lawOf (Measure.pi fun _ : Fin n => ν) (fun θ' x => ∏ i, p θ' (x i)) θ) := by
    intro i
    exact integral_finsetSum (s := (Finset.univ : Finset (Fin n)))
      (f := fun (j : Fin n) (x : Fin n → 𝓧) => score p θ (x i) * score p θ (x j))
      (fun j _ => hint i j)
  rw [hsplit_outer]
  simp only [hsplit_inner]
  have hval : ∀ i j, (∫ x : Fin n → 𝓧, (score p θ (x i) * score p θ (x j))
        ∂(lawOf (Measure.pi fun _ : Fin n => ν) (fun θ' x => ∏ i, p θ' (x i)) θ))
      = (if i = j then fisherInformation ν p θ else 0) := by
    intro i j
    have hwd : (∫ x : Fin n → 𝓧, (score p θ (x i) * score p θ (x j))
          ∂(lawOf (Measure.pi fun _ : Fin n => ν) (fun θ' x => ∏ i, p θ' (x i)) θ))
        = ∫ x : Fin n → 𝓧, (ENNReal.ofReal (∏ k, p θ (x k))).toReal
          • (score p θ (x i) * score p θ (x j)) ∂(Measure.pi fun _ : Fin n => ν) := by
      have h := integral_withDensity_eq_integral_toReal_smul
        (μ := Measure.pi fun _ : Fin n => ν)
        (f := fun x : Fin n → 𝓧 => ENNReal.ofReal (∏ k, p θ (x k)))
        ((joint_meas n hp_meas).ennreal_ofReal)
        (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)
        (fun x : Fin n → 𝓧 => score p θ (x i) * score p θ (x j))
      exact h
    rw [hwd]
    have hpt : (fun x : Fin n → 𝓧 => (ENNReal.ofReal (∏ k, p θ (x k))).toReal
          • (score p θ (x i) * score p θ (x j)))
        = fun x => ∏ k, crossFactor p θ n i j k (x k) :=
      funext fun x => integrand_eq_factor_prod n hp_pos i j x
    rw [hpt]
    have hfac : (∫ x : Fin n → 𝓧, ∏ k, crossFactor p θ n i j k (x k)
          ∂(Measure.pi fun _ : Fin n => ν))
        = ∏ k, ∫ y, crossFactor p θ n i j k y ∂ν :=
      integral_fintype_prod_eq_prod (μ := fun _ : Fin n => ν)
        (fun k (y : 𝓧) => crossFactor p θ n i j k y)
    rw [hfac]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl]
      have h0 : ∀ b ∈ (Finset.univ : Finset (Fin n)), b ≠ i →
          (∫ y, crossFactor p θ n i i b y ∂ν) = 1 :=
        fun b _ hbi => factor_val_off n hp_pos hp_meas hnorm i i b hbi hbi
      have h1 : i ∉ (Finset.univ : Finset (Fin n)) →
          (∫ y, crossFactor p θ n i i i y ∂ν) = 1 :=
        fun h => absurd (Finset.mem_univ i) h
      have he := Finset.prod_eq_single (s := (Finset.univ : Finset (Fin n)))
        (f := fun k => ∫ y, crossFactor p θ n i i k y ∂ν) i h0 h1
      exact he.trans (factor_val_diag n hp_pos hp_meas hp_diff i i rfl)
    · rw [ite_eq_right hij]
      have hzero : (∏ k, ∫ y, crossFactor p θ n i j k y ∂ν) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i)
          (factor_val_cross n hp_pos hp_meas hmean i j hij)
      exact hzero
  simp only [hval]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end MathlibExt.Probability.Statistics.FisherInformation
