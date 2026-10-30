/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.PSeries

import MathlibExt.Analysis.Fourier.AddCircle.RiemannLebesgue

/-!
# Fourier coefficients of a `C¹` periodic function are absolutely summable

For a `T`-periodic function `f : ℝ → ℂ` that is differentiable everywhere with
continuous derivative `f'`, the Fourier coefficients satisfy
`ĉₙ(f) = (T / (2π i n)) · ĉₙ(f')` for `n ≠ 0`. Since `f'` is square-integrable
on one period, Parseval's identity gives `∑ ‖ĉₙ(f')‖² < ∞`, and Cauchy–Schwarz
(in the form `2ab ≤ a² + b²`) against the `ℓ²` sequence `1 / |n|` yields
`∑ ‖ĉₙ(f)‖ < ∞`. Mathlib's `hasSum_fourier_series_of_summable` then gives
uniform convergence of the Fourier series of `f` to `f` on the circle, and
pointwise convergence on any one period. The coefficient decay proof reuses
`RiemannLebesgue.tendsto_fourierCoeffOn_cofinite` for the interval-integrable derivative.

Source: companion to the Fejér section of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/FourierSeries.lean`
(Theorem (Fejér), April 22, 2021). It is not one of the 72 v1 targets, and it
is not in the pinned Mathlib: Mathlib has the implication
`summable coefficients ⇒ uniform convergence`
(`hasSum_fourier_series_of_summable`) and Parseval's identity
(`hasSum_sq_fourierCoeffOn`), but no statement that a `C¹` periodic function
has summable Fourier coefficients.
-/

@[expose] public section

namespace MathlibExt.Analysis.Fourier.AddCircle.C1FourierSummable

open MeasureTheory Filter Topology

/-- A continuous function on `ℝ` is square-integrable on one period. -/
theorem memLp_of_continuousOn_Ioc {T : ℝ} {g : ℝ → ℂ}
    (hg : Continuous g) : MemLp g 2 (volume.restrict (Set.Ioc 0 T)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
  apply MemLp.of_bound _ C
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hC x (Set.Ioc_subset_Icc_self hx)
  · exact hg.aestronglyMeasurable.restrict

/-- A `T`-periodic continuous function descends to a continuous function on the
circle `AddCircle T`, via `AddCircle.liftIoc`. -/
noncomputable def liftPeriodicContinuousMap {T : ℝ} [hT' : Fact (0 < T)]
    {f : ℝ → ℂ}
    (hper : Function.Periodic f T) (hfcont : Continuous f) : C(AddCircle T, ℂ) :=
  ⟨AddCircle.liftIoc T 0 f,
    AddCircle.liftIoc_continuous (hper 0).symm hfcont.continuousOn⟩

/-- The descended function agrees with `f` on the period `(0, T]`. -/
theorem liftPeriodicContinuousMap_apply {T : ℝ} [hT' : Fact (0 < T)]
    {f : ℝ → ℂ}
    (hper : Function.Periodic f T) (hfcont : Continuous f) {x : ℝ}
    (hx : x ∈ Set.Ioc 0 T) :
    liftPeriodicContinuousMap hper hfcont (x : AddCircle T) = f x :=
  AddCircle.liftIoc_zero_coe_apply hx

/-- The interval coefficients on `(0, 0 + T]` agree with those on `(0, T]`; this
bridges Mathlib's `fourierCoeff_liftIoc_eq`, which is stated on `(a, a + T]`. -/
theorem fourierCoeffOn_zero_add {T : ℝ} [hT' : Fact (0 < T)] {f : ℝ → ℂ} (hT : 0 < T) :
    fourierCoeffOn (lt_add_of_pos_right (0 : ℝ) (Fact.out : (0 : ℝ) < T)) f =
      fourierCoeffOn hT f := by
  funext n
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp only [fourier_coe_apply, zero_add, sub_zero]

/-- The Fourier coefficients of the descended function are the interval
coefficients `fourierCoeffOn`. -/
theorem fourierCoeff_liftPeriodicContinuousMap {T : ℝ} (hT : 0 < T) [hT' : Fact (0 < T)]
    {f : ℝ → ℂ}
    (hper : Function.Periodic f T) (hfcont : Continuous f) (n : ℤ) :
    fourierCoeff (liftPeriodicContinuousMap hper hfcont) n = fourierCoeffOn hT f n := by
  show fourierCoeff (AddCircle.liftIoc T 0 f) n = fourierCoeffOn hT f n
  rw [← fourierCoeffOn_zero_add hT]
  exact fourierCoeff_liftIoc_eq (T := T) (a := 0) f n

/-- A Fourier coefficient bounded by the sup norm on one period. -/
theorem norm_fourierCoeffOn_le_of_bound {a b : ℝ} (hab : a < b) {f : ℝ → ℂ} {C : ℝ}
    (hC : ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ C) (n : ℤ) :
    ‖fourierCoeffOn hab f n‖ ≤ max C 0 := by
  rw [fourierCoeffOn_eq_integral]
  have hnorm : ∀ x ∈ Set.uIoc a b,
      ‖fourier (-n) (x : AddCircle (b - a)) • f x‖ ≤ max C 0 := by
    intro x hx
    rw [Set.uIoc_of_le hab.le] at hx
    have hxIcc : x ∈ Set.Icc a b := Set.Ioc_subset_Icc_self hx
    rw [norm_smul]
    have h1 : ‖(fourier (-n) (x : AddCircle (b - a)) : ℂ)‖ = 1 := by
      rw [fourier_apply]
      exact Circle.norm_coe _
    rw [h1, one_mul]
    exact le_trans (hC x hxIcc) (le_max_left _ _)
  calc ‖(1 / (b - a)) • ∫ x in a..b, fourier (-n) (x : AddCircle (b - a)) • f x‖
      = (1 / (b - a)) * ‖∫ x in a..b, fourier (-n) (x : AddCircle (b - a)) • f x‖ := by
        rw [norm_smul,
          Real.norm_of_nonneg (div_nonneg zero_le_one (sub_nonneg.mpr hab.le))]
    _ ≤ (1 / (b - a)) * (max C 0 * |b - a|) :=
        mul_le_mul_of_nonneg_left
          (intervalIntegral.norm_integral_le_of_norm_le_const hnorm)
          (div_nonneg zero_le_one (sub_nonneg.mpr hab.le))
    _ = max C 0 := by
        have hba : (b : ℝ) - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
        rw [abs_of_pos (sub_pos.mpr hab), mul_comm (1 / (b - a)) (max C 0 * (b - a)),
          mul_assoc, mul_one_div_cancel hba, mul_one]

/-- **Coefficient identity for a `C¹` periodic function.** For `n ≠ 0`,
`ĉₙ(f) = (T / (2π i n)) · ĉₙ(f')`. The boundary term in integration by parts
vanishes by periodicity. -/
theorem fourierCoeffOn_eq_of_hasDerivAt {T : ℝ} (hT : 0 < T) {f f' : ℝ → ℂ}
    (hper : Function.Periodic f T)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume 0 T)
    {n : ℤ} (hn : n ≠ 0) :
    fourierCoeffOn hT f n =
      (T / (2 * Real.pi * Complex.I * n)) * fourierCoeffOn hT f' n := by
  have hT0 : f T = f 0 := by
    have h := hper 0
    simpa using h
  have h := fourierCoeffOn_of_hasDerivAt hT hn (fun x _ => hderiv x) hf'
  rw [h, hT0, sub_self, mul_zero, zero_sub]
  simp only [Complex.ofReal_zero, sub_zero]
  have hne : (2 : ℂ) * Real.pi * Complex.I * (n : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
    · norm_num
    · exact Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    · exact Complex.I_ne_zero
    · exact_mod_cast hn
  have hne' : (-2 : ℂ) * Real.pi * Complex.I * (n : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
    · norm_num
    · exact Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    · exact Complex.I_ne_zero
    · exact_mod_cast hn
  field_simp [hne, hne']

/-- **Norm form of the coefficient identity.** -/
theorem norm_fourierCoeffOn_eq_of_hasDerivAt {T : ℝ} (hT : 0 < T) {f f' : ℝ → ℂ}
    (hper : Function.Periodic f T)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume 0 T)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeffOn hT f n‖ =
      (T / (2 * Real.pi * |(n : ℝ)|)) * ‖fourierCoeffOn hT f' n‖ := by
  rw [fourierCoeffOn_eq_of_hasDerivAt hT hper hderiv hf' hn, norm_mul]
  congr 1
  rw [norm_div]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hTn : ‖(T : ℂ)‖ = T := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  have hden : ‖(2 : ℂ) * Real.pi * Complex.I * (n : ℂ)‖ = 2 * Real.pi * |(n : ℝ)| := by
    simp [abs_of_pos Real.pi_pos]
  rw [hTn, hden]

/-- **Fourier coefficients of a `C¹` periodic function are absolutely summable.** -/
theorem summable_fourierCoeffOn_of_hasDerivAt {T : ℝ} (hT : 0 < T) {f f' : ℝ → ℂ}
    (hper : Function.Periodic f T)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf'cont : Continuous f') :
    Summable (fourierCoeffOn hT f) := by
  apply Summable.of_norm
  have hf'int : IntervalIntegrable f' volume 0 T := hf'cont.intervalIntegrable 0 T
  have hSq : Summable (fun n : ℤ => ‖fourierCoeffOn hT f' n‖ ^ 2) :=
    (hasSum_sq_fourierCoeffOn hT (memLp_of_continuousOn_Ioc hf'cont)).summable
  have hP : Summable (fun n : ℤ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
  have hBound : Summable (fun n : ℤ =>
      (T / (4 * Real.pi)) * (‖fourierCoeffOn hT f' n‖ ^ 2 + 1 / (n : ℝ) ^ 2)) :=
    Summable.mul_left _ (Summable.add hSq hP)
  have hPoint : Summable (fun n : ℤ =>
      if n = 0 then ‖fourierCoeffOn hT f 0‖ else 0) := by
    apply summable_of_hasFiniteSupport
    apply Set.Finite.subset (Set.finite_singleton (0 : ℤ))
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    by_contra hne
    have hn0 : n ≠ 0 := by simpa using hne
    simp only [hn0, ite_false] at hn
    exact hn trivial
  apply Summable.of_nonneg_of_le (g := fun n : ℤ => ‖fourierCoeffOn hT f n‖)
    (f := fun n : ℤ => (T / (4 * Real.pi)) *
      (‖fourierCoeffOn hT f' n‖ ^ 2 + 1 / (n : ℝ) ^ 2) +
        (if n = 0 then ‖fourierCoeffOn hT f 0‖ else 0))
  · intro n
    exact norm_nonneg _
  · intro n
    by_cases hn : n = 0
    · subst hn
      simp only [ite_true]
      have h1 : (0:ℝ) ≤ (T / (4 * Real.pi)) *
          (‖fourierCoeffOn hT f' 0‖ ^ 2 + 1 / ((0 : ℤ) : ℝ) ^ 2) := by positivity
      exact le_add_of_nonneg_left h1
    · simp only [hn, ite_false]
      rw [add_zero]
      have hnorm := norm_fourierCoeffOn_eq_of_hasDerivAt hT hper hderiv hf'int hn
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have hAbs : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr hnR
      have hAM : 2 * ‖fourierCoeffOn hT f' n‖ * (|(n : ℝ)|)⁻¹ ≤
          ‖fourierCoeffOn hT f' n‖ ^ 2 + ((|(n : ℝ)|)⁻¹) ^ 2 :=
        two_mul_le_add_pow_two _ _
      have hC : (0:ℝ) ≤ T / (4 * Real.pi) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hAM hC
      have hEq : (T / (4 * Real.pi)) * (2 * ‖fourierCoeffOn hT f' n‖ * (|(n : ℝ)|)⁻¹) =
          (T / (2 * Real.pi * |(n : ℝ)|)) * ‖fourierCoeffOn hT f' n‖ := by
        field_simp [hAbs]
        ring
      have hSqEq : ((|(n : ℝ)|)⁻¹) ^ 2 = 1 / (n : ℝ) ^ 2 := by
        rw [inv_pow, sq_abs, one_div]
      rw [hnorm, ← hEq]
      calc (T / (4 * Real.pi)) * (2 * ‖fourierCoeffOn hT f' n‖ * (|(n : ℝ)|)⁻¹)
          ≤ (T / (4 * Real.pi)) * (‖fourierCoeffOn hT f' n‖ ^ 2 + ((|(n : ℝ)|)⁻¹) ^ 2) :=
            hmul
        _ = (T / (4 * Real.pi)) * (‖fourierCoeffOn hT f' n‖ ^ 2 + 1 / (n : ℝ) ^ 2) := by
            rw [hSqEq]
  · exact hBound.add hPoint

/-- **Decay rate:** `n · ‖ĉₙ(f)‖ → 0` along the cofinite filter. -/
theorem tendsto_mul_norm_fourierCoeffOn_of_hasDerivAt {T : ℝ} (hT : 0 < T)
    {f f' : ℝ → ℂ}
    (hper : Function.Periodic f T)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf'cont : Continuous f') :
    Filter.Tendsto (fun n : ℤ => (n : ℝ) * ‖fourierCoeffOn hT f n‖)
      Filter.cofinite (nhds 0) := by
  have hf'int : IntervalIntegrable f' volume 0 T := hf'cont.intervalIntegrable 0 T
  have hToZero : Filter.Tendsto (fun n : ℤ => ‖fourierCoeffOn hT f' n‖)
      Filter.cofinite (nhds 0) := by
    simpa only [norm_zero] using
      (RiemannLebesgue.tendsto_fourierCoeffOn_cofinite hT hf'int).norm
  have hScaled : Filter.Tendsto (fun n : ℤ => (T / (2 * Real.pi)) * ‖fourierCoeffOn hT f' n‖)
      Filter.cofinite (nhds ((T / (2 * Real.pi)) * 0)) := hToZero.const_mul _
  rw [mul_zero] at hScaled
  apply squeeze_zero_norm _ hScaled
  intro n
  by_cases hn : n = 0
  · subst hn
    simp only [Int.cast_zero, zero_mul, norm_zero]
    exact mul_nonneg (div_nonneg hT.le (by positivity : (0:ℝ) ≤ 2 * Real.pi))
      (norm_nonneg _)
  · have hnorm := norm_fourierCoeffOn_eq_of_hasDerivAt hT hper hderiv hf'int hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hAbs : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr hnR
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _)]
    rw [hnorm]
    have h1 : |(n : ℝ)| * ((T / (2 * Real.pi * |(n : ℝ)|)) * ‖fourierCoeffOn hT f' n‖) =
        (T / (2 * Real.pi)) * ‖fourierCoeffOn hT f' n‖ := by
      field_simp [hAbs]
    rw [h1]

/-- **Uniform convergence:** the Fourier series of a `C¹` periodic function
converges uniformly (in `C(AddCircle T, ℂ)`) to `f` on the circle. -/
theorem hasSum_fourier_series_of_hasDerivAt {T : ℝ} (hT : 0 < T) [hT' : Fact (0 < T)]
    {f f' : ℝ → ℂ}
    (hper : Function.Periodic f T) (hfcont : Continuous f)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf'cont : Continuous f') :
    HasSum (fun n : ℤ => fourierCoeffOn hT f n • (fourier n : C(AddCircle T, ℂ)))
      (liftPeriodicContinuousMap hper hfcont) := by
  have hsumm : Summable (fun n : ℤ =>
      fourierCoeff (liftPeriodicContinuousMap hper hfcont) n) := by
    have hEq : (fun n : ℤ => fourierCoeff (liftPeriodicContinuousMap hper hfcont) n) =
        fourierCoeffOn hT f := by
      funext n
      exact fourierCoeff_liftPeriodicContinuousMap hT hper hfcont n
    rw [hEq]
    exact summable_fourierCoeffOn_of_hasDerivAt hT hper hderiv hf'cont
  have h := hasSum_fourier_series_of_summable hsumm
  convert h using 1
  ext n
  rw [fourierCoeff_liftPeriodicContinuousMap hT hper hfcont n]

/-- **Pointwise convergence on one period.** -/
theorem hasSum_fourier_series_of_hasDerivAt_apply {T : ℝ} (hT : 0 < T)
    [hT' : Fact (0 < T)] {f f' : ℝ → ℂ}
    (hper : Function.Periodic f T) (hfcont : Continuous f)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf'cont : Continuous f') {x : ℝ} (hx : x ∈ Set.Ioc 0 T) :
    HasSum (fun n : ℤ => fourierCoeffOn hT f n • (fourier n (x : AddCircle T) : ℂ))
      (f x) := by
  have h := hasSum_fourier_series_of_hasDerivAt hT hper hfcont hderiv hf'cont
  have h2 := (ContinuousMap.evalCLM ℂ (x : AddCircle T)).hasSum h
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, smul_eq_mul,
    liftPeriodicContinuousMap_apply hper hfcont hx] at h2
  exact h2

end MathlibExt.Analysis.Fourier.AddCircle.C1FourierSummable
