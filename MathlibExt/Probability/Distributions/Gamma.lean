/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul

open MeasureTheory Set Filter Topology

open scoped ENNReal NNReal

namespace ProbabilityTheory

@[expose] public section

noncomputable section

lemma toReal_gammaPDF {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    (gammaPDF a r x).toReal = gammaPDFReal a r x := by
  rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)]

lemma measurable_gammaPDF (a r : ℝ) : Measurable (gammaPDF a r) :=
  Measurable.ennreal_ofReal (measurable_gammaPDFReal a r)

lemma gammaPDF_lt_top (a r x : ℝ) : gammaPDF a r x < ∞ := by
  simp [gammaPDF]

lemma integral_gammaMeasure_eq_integral_smul {a r : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    ∫ x, f x ∂(gammaMeasure a r)
      = ∫ x, (gammaPDF a r x).toReal • f x ∂volume := by
  rw [gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul (measurable_gammaPDF a r)
      (ae_of_all _ fun _ => gammaPDF_lt_top a r _)]

theorem integrable_gammaMeasure_iff {a r : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℝ → E} :
    Integrable g (gammaMeasure a r)
      ↔ Integrable (fun x => (gammaPDF a r x).toReal • g x) volume := by
  rw [gammaMeasure]
  exact (integrable_withDensity_iff_integrable_smul' (measurable_gammaPDF a r)
    (ae_of_all _ fun _ => gammaPDF_lt_top a r _))

/-- Scaled gamma integrand is integrable on `Ioi 0`. This generalizes
`Real.GammaIntegral_convergent` (rate `1`) to any positive rate `s`. -/
theorem integrableOn_rpow_mul_exp_neg_mul_Ioi {a s : ℝ} (ha : 0 < a)
    (hs : 0 < s) :
    IntegrableOn (fun x : ℝ => x ^ (a - 1) * Real.exp (-(s * x))) (Ioi 0) := by
  have hbase : IntegrableOn (fun y : ℝ => y ^ (a - 1) * Real.exp (-y)) (Ioi 0) := by
    have h := Real.GammaIntegral_convergent ha
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    rw [mul_comm]
  have hcomp : IntegrableOn (fun x : ℝ => (s * x) ^ (a - 1) * Real.exp (-(s * x)))
      (Ioi 0) := by
    have hiff := integrableOn_Ioi_comp_mul_left_iff
      (fun y : ℝ => y ^ (a - 1) * Real.exp (-y)) (0 : ℝ) hs
    simp only [mul_zero] at hiff
    exact hiff.mpr hbase
  have hfactor : ∀ x : ℝ, 0 < x →
      x ^ (a - 1) * Real.exp (-(s * x))
        = (s ^ (a - 1))⁻¹ * ((s * x) ^ (a - 1) * Real.exp (-(s * x))) := by
    intro x hx
    have hmul : (s * x) ^ (a - 1) = s ^ (a - 1) * x ^ (a - 1) :=
      Real.mul_rpow hs.le hx.le
    have hs0 : s ^ (a - 1) ≠ 0 := (Real.rpow_pos_of_pos hs _).ne'
    field_simp
    rw [hmul]
    ring
  have hconst : IntegrableOn
      (fun x : ℝ => (s ^ (a - 1))⁻¹ * ((s * x) ^ (a - 1) * Real.exp (-(s * x))))
      (Ioi 0) :=
    hcomp.const_mul _
  refine hconst.congr_fun (fun x hx => ?_) measurableSet_Ioi
  exact (hfactor x hx).symm

/-- Exponential moments of a gamma law exist below the rate. -/
theorem integrable_exp_mul_gammaMeasure {a r t : ℝ} (ha : 0 < a) (hr : 0 < r)
    (ht : t < r) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (gammaMeasure a r) := by
  rw [integrable_gammaMeasure_iff]
  have htoReal : ∀ x : ℝ, (gammaPDF a r x).toReal = gammaPDFReal a r x :=
    fun x => toReal_gammaPDF ha hr x
  simp_rw [htoReal, smul_eq_mul]
  have hfun : (fun x : ℝ => gammaPDFReal a r x * Real.exp (t * x))
      = fun x => if 0 ≤ x then
        (r ^ a / Real.Gamma a) * (x ^ (a - 1) * Real.exp (-((r - t) * x)))
        else 0 := by
    funext x
    unfold gammaPDFReal
    by_cases hx : 0 ≤ x
    · simp only [hx, ite_true]
      have hexp : Real.exp (-(r * x)) * Real.exp (t * x)
          = Real.exp (-((r - t) * x)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x)) * Real.exp (t * x)
          = (r ^ a / Real.Gamma a) *
            (x ^ (a - 1) * (Real.exp (-(r * x)) * Real.exp (t * x))) := by ring
        _ = (r ^ a / Real.Gamma a) *
            (x ^ (a - 1) * Real.exp (-((r - t) * x))) := by rw [hexp]
    · simp [hx]
  rw [hfun]
  rw [← integrableOn_univ]
  rw [← Iio_union_Ici (a := (0 : ℝ)), integrableOn_union]
  constructor
  · have hzero : EqOn (0 : ℝ → ℝ)
        (fun x => if 0 ≤ x then (r ^ a / Real.Gamma a) *
          (x ^ (a - 1) * Real.exp (-((r - t) * x))) else 0) (Iio 0) := by
      intro x hx
      simp only [mem_Iio] at hx
      simp only [Pi.zero_apply]
      rw [ite_eq_right (by linarith : ¬ (0 : ℝ) ≤ x)]
    exact integrableOn_zero.congr_fun hzero measurableSet_Iio
  · have hs : 0 < r - t := sub_pos.mpr ht
    have hIoi := integrableOn_rpow_mul_exp_neg_mul_Ioi (a := a) (s := r - t) ha hs
    have hmul := hIoi.const_mul (r ^ a / Real.Gamma a)
    have hcongr : EqOn
        (fun x : ℝ => (r ^ a / Real.Gamma a) *
          (x ^ (a - 1) * Real.exp (-((r - t) * x))))
        (fun x => if 0 ≤ x then (r ^ a / Real.Gamma a) *
            (x ^ (a - 1) * Real.exp (-((r - t) * x))) else 0) (Ici 0) := by
      intro x hx
      simp only [mem_Ici] at hx
      dsimp only
      rw [ite_eq_left hx]
    have hIci : IntegrableOn
        (fun x : ℝ => (r ^ a / Real.Gamma a) *
          (x ^ (a - 1) * Real.exp (-((r - t) * x)))) (Ici 0) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact hmul
    exact hIci.congr_fun hcongr measurableSet_Ici

/-- MGF of a gamma law below the rate. -/
theorem mgf_gammaMeasure_of_lt {a r t : ℝ} (ha : 0 < a) (hr : 0 < r)
    (ht : t < r) :
    mgf id (gammaMeasure a r) t = (r / (r - t)) ^ a := by
  have hInt : Integrable (fun x : ℝ => Real.exp (t * x)) (gammaMeasure a r) :=
    integrable_exp_mul_gammaMeasure ha hr ht
  rw [mgf, integral_gammaMeasure_eq_integral_smul]
  have htoReal : ∀ x : ℝ, (gammaPDF a r x).toReal = gammaPDFReal a r x :=
    fun x => toReal_gammaPDF ha hr x
  simp_rw [htoReal, smul_eq_mul, id_eq]
  have hfun : (fun x : ℝ => gammaPDFReal a r x * Real.exp (t * x))
      = fun x => if 0 ≤ x then
        (r ^ a / Real.Gamma a) * (x ^ (a - 1) * Real.exp (-((r - t) * x)))
        else 0 := by
    funext x
    unfold gammaPDFReal
    by_cases hx : 0 ≤ x
    · simp only [hx, ite_true]
      have hexp : Real.exp (-(r * x)) * Real.exp (t * x)
          = Real.exp (-((r - t) * x)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x)) * Real.exp (t * x)
          = (r ^ a / Real.Gamma a) *
            (x ^ (a - 1) * (Real.exp (-(r * x)) * Real.exp (t * x))) := by ring
        _ = (r ^ a / Real.Gamma a) *
            (x ^ (a - 1) * Real.exp (-((r - t) * x))) := by rw [hexp]
    · simp [hx]
  rw [hfun]
  set f : ℝ → ℝ := fun x => if 0 ≤ x then
    (r ^ a / Real.Gamma a) * (x ^ (a - 1) * Real.exp (-((r - t) * x))) else 0 with hf
  have hIntF : Integrable f volume := by
    have h := (integrable_gammaMeasure_iff (a := a) (r := r)
      (g := fun x : ℝ => Real.exp (t * x))).mp hInt
    simp_rw [htoReal, smul_eq_mul] at h
    rwa [hfun] at h
  have hIio : IntegrableOn f (Iio 0) := hIntF.integrableOn
  have hIci : IntegrableOn f (Ici 0) := hIntF.integrableOn
  have hsplit := intervalIntegral.integral_Iio_add_Ici hIio hIci
  have hIio_zero : ∫ x in Iio (0 : ℝ), f x = 0 := by
    apply setIntegral_eq_zero_of_ae_eq_zero
    filter_upwards with x hx
    simp only [mem_Iio] at hx
    simp [hf, ite_eq_right (by linarith : ¬ (0 : ℝ) ≤ x)]
  have hIci_eq : ∫ x in Ici (0 : ℝ), f x
      = ∫ x in Ioi (0 : ℝ), (r ^ a / Real.Gamma a) *
        (x ^ (a - 1) * Real.exp (-((r - t) * x))) := by
    rw [integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [mem_Ioi] at hx
    simp [hf, ite_eq_left hx.le]
  have hIoi_val : ∫ x in Ioi (0 : ℝ), (r ^ a / Real.Gamma a) *
        (x ^ (a - 1) * Real.exp (-((r - t) * x)))
      = (r / (r - t)) ^ a := by
    have hs : 0 < r - t := sub_pos.mpr ht
    rw [integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi ha hs]
    have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
    have hr0 : (0 : ℝ) ≤ r := hr.le
    have hs0 : (0 : ℝ) ≤ (r - t)⁻¹ := (inv_pos.mpr hs).le
    have hmul : r ^ a * ((r - t)⁻¹) ^ a = (r / (r - t)) ^ a := by
      rw [div_eq_mul_inv, ← Real.mul_rpow hr0 hs0]
    have h12 : (1 / (r - t)) ^ a = ((r - t)⁻¹) ^ a := by
      rw [one_div]
    calc r ^ a / Real.Gamma a * ((1 / (r - t)) ^ a * Real.Gamma a)
        = (r ^ a * ((r - t)⁻¹) ^ a) * (Real.Gamma a / Real.Gamma a) := by
          rw [h12]
          ring
      _ = (r / (r - t)) ^ a := by
          rw [div_self hG, mul_one]
          exact hmul
  calc ∫ x, f x
      = (∫ x in Iio (0 : ℝ), f x) + ∫ x in Ici (0 : ℝ), f x := hsplit.symm
    _ = ∫ x in Ioi (0 : ℝ), (r ^ a / Real.Gamma a) *
          (x ^ (a - 1) * Real.exp (-((r - t) * x))) := by
        rw [hIio_zero, zero_add, hIci_eq]
    _ = (r / (r - t)) ^ a := hIoi_val

/-- Below the rate, exponential moments exist; hence `Iio r` lies in the
integrability set for MGF uniqueness. -/
theorem Iio_subset_integrableExpSet_gammaMeasure {a r : ℝ} (ha : 0 < a)
    (hr : 0 < r) :
    Iio r ⊆ integrableExpSet id (gammaMeasure a r) := by
  intro t ht
  simp only [mem_Iio] at ht
  simp only [integrableExpSet, mem_ofPred_eq, id_eq]
  exact integrable_exp_mul_gammaMeasure ha hr ht

/-- A symmetric interval around zero lies in the interior of the gamma
integrability set, as required by `measure_eq_of_mgf_eqOn_Ioo`. -/
theorem Ioo_subset_interior_integrableExpSet_gammaMeasure {a r ε : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hε : 0 < ε) (hεr : ε < r) :
    Ioo (-ε) ε ⊆ interior (integrableExpSet id (gammaMeasure a r)) := by
  have _ : 0 < ε := hε
  have hIio := isOpen_Iio.subset_interior_iff.mpr
    (Iio_subset_integrableExpSet_gammaMeasure ha hr (r := r))
  intro t ht
  simp only [mem_Ioo] at ht
  apply hIio
  simp only [mem_Iio]
  linarith

theorem not_integrable_exp_mul_gammaMeasure {a r t : ℝ} (ha : 0 < a) (hr : 0 < r)
    (ht : r ≤ t) : ¬ Integrable (fun x : ℝ => Real.exp (t * x)) (gammaMeasure a r) := by
  intro h
  rw [integrable_gammaMeasure_iff] at h
  have hon : IntegrableOn (fun x : ℝ => x ^ (a - 1)) (Ioi 1) := by
    refine Integrable.mono' ((h.integrableOn (s := Ioi 1)).const_mul (r ^ a / Real.Gamma a)⁻¹)
      (by fun_prop) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := lt_trans one_pos hx
    rw [toReal_gammaPDF ha hr, gammaPDFReal, ite_eq_left hx0.le, smul_eq_mul,
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    have he : 1 ≤ Real.exp (-(r * x)) * Real.exp (t * x) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    have hxa : 0 ≤ x ^ (a - 1) := Real.rpow_nonneg hx0.le _
    calc x ^ (a - 1) ≤ x ^ (a - 1) * (Real.exp (-(r * x)) * Real.exp (t * x)) :=
          le_mul_of_one_le_right hxa he
      _ = (r ^ a / Real.Gamma a)⁻¹ *
          (r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x)) * Real.exp (t * x)) := by
          field_simp
  have := (integrableOn_Ioi_rpow_iff one_pos).1 hon
  linarith

/-- The exponential moment `E[exp (t X)]` of a gamma `(a, r)` law is finite exactly for
`t < r`. -/
theorem integrableExpSet_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    integrableExpSet id (gammaMeasure a r) = Iio r := by
  ext t
  refine ⟨fun h => ?_, fun h => Iio_subset_integrableExpSet_gammaMeasure ha hr h⟩
  by_contra h'
  exact not_integrable_exp_mul_gammaMeasure ha hr (not_lt.1 h') h

/-- MGF uniqueness for gamma laws: a real probability law whose MGF equals the gamma `(a, r)`
MGF as a function on all of `ℝ` (both vanish where the exponential moment is infinite) is that
gamma law. -/
theorem eq_gammaMeasure_of_mgf_eq {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (h : mgf id ν = mgf id (gammaMeasure a r)) :
    ν = gammaMeasure a r := by
  have := isProbabilityMeasure_gammaMeasure ha hr
  have hS : integrableExpSet id ν = Iio r := by
    rw [integrableExpSet_eq_of_mgf h, integrableExpSet_gammaMeasure ha hr]
  apply Measure.ext_of_complexMGF_id_eq
  funext z
  by_cases hz : z.re < r
  · exact eqOn_complexMGF_of_mgf h (by rw [hS, interior_Iio]; exact hz)
  · rw [complexMGF_undef aemeasurable_id, complexMGF_undef aemeasurable_id]
    · exact not_integrable_exp_mul_gammaMeasure ha hr (not_lt.1 hz)
    · intro hi
      have : z.re ∈ integrableExpSet id ν := hi
      rw [hS] at this
      exact hz this

end

end

end ProbabilityTheory
