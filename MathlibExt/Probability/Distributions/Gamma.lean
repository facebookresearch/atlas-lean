/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.RingTheory.Polynomial.Pochhammer

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


/-- Generic Gamma moments and integrals (moved here from the negative
binomial development, which uses them for the Gamma–Poisson mixture). -/

/-- `Γ(a + k) = a⁽ᵏ⁾ Γ(a)` for `a > 0`. -/
lemma Gamma_add_nat_eq {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Real.Gamma (a + k) = (Polynomial.ascPochhammer ℝ k).eval a * Real.Gamma a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one (by positivity), ih,
      Polynomial.ascPochhammer_succ_eval]
    ring

/-- `rᵏ r^(a - 1) = r^(a + k - 1)` for `r ≥ 0` and `a > 0`. -/
lemma pow_mul_rpow_sub_one {r a : ℝ} (hr : 0 ≤ r) (ha : 0 < a) (k : ℕ) :
    r ^ k * r ^ (a - 1) = r ^ (a + k - 1) := by
  rcases hr.eq_or_lt with rfl | hr
  · rcases k with _ | k
    · simp
    · rw [zero_pow (Nat.succ_ne_zero k), zero_mul, Real.zero_rpow]
      push_cast
      linarith
  · rw [← Real.rpow_natCast, ← Real.rpow_add hr]
    ring_nf

/-- The Gamma law is concentrated on `[0, ∞)`. -/
theorem ae_nonneg_gammaMeasure (a b : ℝ) : ∀ᵐ x ∂gammaMeasure a b, 0 ≤ x := by
  rw [gammaMeasure, ae_withDensity_iff (measurable_gammaPDF a b)]
  refine ae_of_all _ fun x hx => ?_
  by_contra h
  exact hx (by simp [gammaPDF, gammaPDFReal, h])

/-- The Gamma density times `x ^ k e^{-c x}` is the indicator of `[0, ∞)` of an explicit
function. -/
private lemma gammaPDF_smul_eq_indicator {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) (x : ℝ) :
    (gammaPDF a b x).toReal • (x ^ k * Real.exp (-(c * x))) =
      Set.indicator (Set.Ici 0)
        (fun x => b ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(b * x)) * (x ^ k * Real.exp (-(c * x)))) x := by
  rw [toReal_gammaPDF ha hb, smul_eq_mul, gammaPDFReal, Set.indicator]
  by_cases hx : 0 ≤ x <;> simp [hx]

/-- On `(0, ∞)` the integrand is `bᵃ / Γ(a) · x^(a + k - 1) e^{-(b + c) x}`. -/
private lemma gamma_integrand_eq {a b c x : ℝ} (ha : 0 < a) (hx : 0 < x) (k : ℕ) :
    b ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(b * x)) * (x ^ k * Real.exp (-(c * x))) =
      b ^ a / Real.Gamma a * (x ^ ((a + k) - 1) * Real.exp (-((b + c) * x))) := by
  rw [← pow_mul_rpow_sub_one hx.le ha k,
    show -((b + c) * x) = -(b * x) + -(c * x) by ring, Real.exp_add]
  ring

/-- For `a, b > 0` and `c ≥ 0`, `x ↦ x ^ k e^{-c x}` is integrable for `Gamma(a, b)`. -/
theorem integrable_pow_mul_exp_neg_mul_gammaMeasure {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 ≤ c) (k : ℕ) :
    Integrable (fun x => x ^ k * Real.exp (-(c * x))) (gammaMeasure a b) := by
  rw [integrable_gammaMeasure_iff, funext (gammaPDF_smul_eq_indicator ha hb k),
    integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
  have h := (integrableOn_rpow_mul_exp_neg_mul_Ioi (a := a + k) (s := b + c) (by positivity)
    (by linarith)).const_mul (b ^ a / Real.Gamma a)
  exact IntegrableOn.congr_fun h (fun x hx => (gamma_integrand_eq ha hx k).symm)
    measurableSet_Ioi

/-- **Gamma integrals.** For shape `a > 0`, rate `b > 0` and `c ≥ 0`,
`∫ x ^ k e^{-c x} dGamma(a, b) = a⁽ᵏ⁾ bᵃ / (b + c) ^ (a + k)`. -/
theorem integral_pow_mul_exp_neg_mul_gammaMeasure {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 ≤ c) (k : ℕ) :
    ∫ x, x ^ k * Real.exp (-(c * x)) ∂gammaMeasure a b =
      (Polynomial.ascPochhammer ℝ k).eval a * b ^ a / (b + c) ^ (a + k) := by
  have hbc : 0 < b + c := by linarith
  rw [integral_gammaMeasure_eq_integral_smul, funext (gammaPDF_smul_eq_indicator ha hb k),
    integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    setIntegral_congr_fun measurableSet_Ioi (fun x hx => gamma_integrand_eq ha hx k),
    integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hbc,
    Gamma_add_nat_eq ha, Real.div_rpow zero_le_one hbc.le, Real.one_rpow]
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have : (b + c) ^ (a + k) ≠ 0 := (Real.rpow_pos_of_pos hbc _).ne'
  field_simp

/-- The mean of `Gamma(a, b)` is `a / b`. -/
theorem integral_id_gammaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x, x ∂gammaMeasure a b = a / b := by
  have h := integral_pow_mul_exp_neg_mul_gammaMeasure ha hb le_rfl 1
  simp only [pow_one, zero_mul, neg_zero, Real.exp_zero, mul_one, add_zero, Polynomial.ascPochhammer_one,
    Polynomial.eval_X, Nat.cast_one] at h
  rw [h, Real.rpow_add hb, Real.rpow_one]
  have : b ^ a ≠ 0 := (Real.rpow_pos_of_pos hb a).ne'
  field_simp

/-- The second moment of `Gamma(a, b)` is `a (a + 1) / b²`. -/
theorem integral_sq_gammaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x, x ^ 2 ∂gammaMeasure a b = a * (a + 1) / b ^ 2 := by
  have h := integral_pow_mul_exp_neg_mul_gammaMeasure ha hb le_rfl 2
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, add_zero] at h
  rw [h, Real.rpow_add hb, Real.rpow_natCast, Polynomial.ascPochhammer_succ_eval, Polynomial.ascPochhammer_one,
    Polynomial.eval_X]
  have : b ^ a ≠ 0 := (Real.rpow_pos_of_pos hb a).ne'
  field_simp
  push_cast
  ring


/-- `x ↦ x` is integrable for `Gamma(a, b)`. -/
theorem integrable_id_gammaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable id (gammaMeasure a b) := by
  have h := integrable_pow_mul_exp_neg_mul_gammaMeasure ha hb le_rfl 1
  simp only [pow_one, zero_mul, neg_zero, Real.exp_zero, mul_one] at h
  exact h

/-- `x ↦ x²` is integrable for `Gamma(a, b)`. -/
theorem integrable_sq_gammaMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun x => x ^ 2) (gammaMeasure a b) := by
  have h := integrable_pow_mul_exp_neg_mul_gammaMeasure ha hb le_rfl 2
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at h
  exact h


end

end

end ProbabilityTheory
