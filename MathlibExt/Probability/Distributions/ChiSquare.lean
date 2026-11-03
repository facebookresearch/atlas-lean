/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Moments.ComplexMGF
public import MathlibExt.Probability.Distributions.Gamma
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul

open MeasureTheory Set Filter Topology

open scoped ENNReal NNReal

namespace ProbabilityTheory

@[expose] public section

noncomputable section

/-- Chi-square law with `p` degrees of freedom, as the gamma law with shape
`p / 2` and scale `2` (rate `1 / 2` in Mathlib's shape-rate convention). -/
noncomputable def chiSquareMeasure (p : ℕ) : Measure ℝ :=
  gammaMeasure ((p : ℝ) / 2) (1 / 2)

theorem isProbabilityMeasure_chiSquareMeasure {p : ℕ} (hp : 0 < p) :
    IsProbabilityMeasure (chiSquareMeasure p) :=
  isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)

/-- MGF of the square of a standard normal variable. Promoted from the private
Johnson–Lindenstrauss development; the formula holds for all `t` with the
convention that both sides vanish for `t ≥ 1/2`. -/
theorem mgf_sq_stdGaussian (t : ℝ) :
    mgf (fun x : ℝ => x ^ 2) (gaussianReal 0 1) t =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  rw [mgf, integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  simp only [smul_eq_mul, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  calc
    (∫ x : ℝ, (√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) *
        Real.exp (t * x ^ 2)) =
        (√(2 * Real.pi))⁻¹ *
          ∫ x : ℝ, Real.exp (-((1 - 2 * t) / 2) * x ^ 2) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf
    _ = (Real.sqrt (1 - 2 * t))⁻¹ := by
      rw [integral_gaussian]
      by_cases h : 0 < 1 - 2 * t
      · rw [Real.sqrt_div (by positivity : 0 ≤ Real.pi)]
        rw [Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ))]
        rw [Real.sqrt_div h.le]
        have htwo : Real.sqrt 2 ≠ 0 := by positivity
        have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
        have hone : Real.sqrt (1 - 2 * t) ≠ 0 := by positivity
        field_simp
      · have hb : (1 - 2 * t) / 2 ≤ 0 := by linarith
        have hs : Real.sqrt (1 - 2 * t) = 0 :=
          Real.sqrt_eq_zero_of_nonpos (le_of_not_gt h)
        have hq : Real.pi / ((1 - 2 * t) / 2) ≤ 0 :=
          div_nonpos_of_nonneg_of_nonpos Real.pi_pos.le hb
        rw [Real.sqrt_eq_zero_of_nonpos hq, hs]
        simp

/-- Exponential moments of the square of a standard normal exist below `1/2`.
Promoted from the private Johnson–Lindenstrauss development. -/
theorem integrable_exp_mul_sq_stdGaussian {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : NNReal) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul, gaussianPDFReal,
    NNReal.coe_one, mul_one, sub_zero]
  have hb : 0 < (1 / 2 : ℝ) - t := by linarith
  convert (integrable_exp_neg_mul_sq hb).const_mul (Real.sqrt (2 * Real.pi))⁻¹ using 1
  funext x
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  ring_nf

/-- The law of the square pushes exponential integrability forward. -/
theorem Iio_subset_integrableExpSet_map_sq_stdGaussian :
    Iio (1 / 2 : ℝ) ⊆
      integrableExpSet id ((gaussianReal 0 1).map fun x : ℝ => x ^ 2) := by
  intro t ht
  simp only [mem_Iio] at ht
  simp only [integrableExpSet, mem_ofPred_eq, id_eq]
  have hsq : Measurable (fun x : ℝ => x ^ 2) := by fun_prop
  have hexp : Measurable (fun y : ℝ => Real.exp (t * y)) :=
    (measurable_const_mul t).exp
  have hiff := integrable_map_measure hexp.aestronglyMeasurable hsq.aemeasurable
    (f := fun x : ℝ => x ^ 2) (g := fun y : ℝ => Real.exp (t * y))
    (μ := gaussianReal 0 1)
  rw [hiff]
  have hcomp : ((fun y : ℝ => Real.exp (t * y)) ∘ fun x : ℝ => x ^ 2)
      = fun x : ℝ => Real.exp (t * x ^ 2) := rfl
  rw [hcomp]
  exact integrable_exp_mul_sq_stdGaussian ht

theorem Ioo_subset_interior_integrableExpSet_map_sq_stdGaussian {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    Ioo (-ε) ε ⊆
      interior (integrableExpSet id ((gaussianReal 0 1).map fun x : ℝ => x ^ 2)) := by
  have _ : 0 < ε := hε
  have hIio := isOpen_Iio.subset_interior_iff.mpr
    Iio_subset_integrableExpSet_map_sq_stdGaussian
  intro t ht
  simp only [mem_Ioo] at ht
  apply hIio
  simp only [mem_Iio]
  linarith

/-- MGF of the pushed-forward square law, via the promoted Gaussian-square MGF. -/
theorem mgf_id_map_sq_stdGaussian (t : ℝ) :
    mgf id ((gaussianReal 0 1).map fun x : ℝ => x ^ 2) t =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  have hsq : AEMeasurable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := by fun_prop
  have h := congrFun (mgf_id_map hsq) t
  rw [h]
  exact mgf_sq_stdGaussian t

/-- The chi-square-one gamma MGF agrees with the Gaussian-square MGF below `1/2`. -/
theorem mgf_gammaMeasure_half_half_eq_sqrt {t : ℝ} (ht : t < 1 / 2) :
    mgf id (gammaMeasure (1 / 2) (1 / 2)) t =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  rw [mgf_gammaMeasure_of_lt (by norm_num) (by norm_num) ht]
  have ha : 0 < 1 - 2 * t := by linarith
  have hbase : (1 / 2 : ℝ) / (1 / 2 - t) = (1 - 2 * t)⁻¹ := by
    field_simp
  rw [hbase, Real.inv_rpow ha.le, ← Real.sqrt_eq_rpow]

/-- MGF of a chi-square law below `1/2`. -/
theorem mgf_chiSquareMeasure_of_lt {p : ℕ} (hp : 0 < p) {t : ℝ}
    (ht : t < 1 / 2) :
    mgf id (chiSquareMeasure p) t
      = ((1 / 2 : ℝ) / (1 / 2 - t)) ^ ((p : ℝ) / 2) := by
  unfold chiSquareMeasure
  exact mgf_gammaMeasure_of_lt (by positivity) (by norm_num) ht

/-- Exponential moments of a chi-square law exist below `1/2`. -/
theorem integrable_exp_mul_chiSquareMeasure {p : ℕ} (hp : 0 < p) {t : ℝ}
    (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (chiSquareMeasure p) := by
  unfold chiSquareMeasure
  exact integrable_exp_mul_gammaMeasure (by positivity) (by norm_num) ht

theorem Iio_subset_integrableExpSet_chiSquareMeasure {p : ℕ} (hp : 0 < p) :
    Iio (1 / 2 : ℝ) ⊆ integrableExpSet id (chiSquareMeasure p) := by
  unfold chiSquareMeasure
  exact Iio_subset_integrableExpSet_gammaMeasure (by positivity) (by norm_num)

theorem Ioo_subset_interior_integrableExpSet_chiSquareMeasure {p : ℕ}
    (hp : 0 < p) {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    Ioo (-ε) ε ⊆ interior (integrableExpSet id (chiSquareMeasure p)) := by
  unfold chiSquareMeasure
  exact Ioo_subset_interior_integrableExpSet_gammaMeasure (by positivity)
    (by norm_num) hε hε2

/-- **The square of a standard normal variable is chi-square with one degree of freedom**, as
an identity of measures on `ℝ`. (Moved here from the likelihood-ratio development so that
both that development and Cochran's theorem reuse one declaration.) -/
theorem gaussianReal_map_sq :
    (gaussianReal 0 1).map (fun x : ℝ => x ^ 2) = chiSquareMeasure 1 := by
  set μ := (gaussianReal 0 1).map (fun x : ℝ => x ^ 2) with hμ
  have : IsProbabilityMeasure (chiSquareMeasure 1) := isProbabilityMeasure_chiSquareMeasure one_pos
  set S : Set ℂ := {z | z.re ∈ Set.Ioo (-(1 / 4 : ℝ)) (1 / 4)} with hS
  have h1 : Set.Ioo (-(1 / 4 : ℝ)) (1 / 4) ⊆ interior (integrableExpSet id μ) :=
    Ioo_subset_interior_integrableExpSet_map_sq_stdGaussian (by norm_num) (by norm_num)
  have h2 : Set.Ioo (-(1 / 4 : ℝ)) (1 / 4) ⊆
      interior (integrableExpSet id (chiSquareMeasure 1)) :=
    Ioo_subset_interior_integrableExpSet_chiSquareMeasure one_pos (by norm_num) (by norm_num)
  have hF : AnalyticOnNhd ℂ (complexMGF id μ) S :=
    analyticOnNhd_complexMGF.mono fun z hz => h1 hz
  have hG : AnalyticOnNhd ℂ (complexMGF id (chiSquareMeasure 1)) S :=
    analyticOnNhd_complexMGF.mono fun z hz => h2 hz
  have hconv : Convex ℝ S := (convex_Ioo _ _).linear_preimage Complex.reLm
  -- the two complex MGFs agree on the strip, by analytic continuation from the reals
  have heq : Set.EqOn (complexMGF id μ) (complexMGF id (chiSquareMeasure 1)) S := by
    refine hF.eqOn_of_preconnected_of_frequently_eq hG hconv.isPreconnected (z₀ := 0)
      (by simp [hS]) ?_
    have h_real : ∃ᶠ (x : ℝ) in 𝓝[≠] (0 : ℝ),
        complexMGF id μ x = complexMGF id (chiSquareMeasure 1) x := by
      have hev : ∀ᶠ x in 𝓝[≠] (0 : ℝ), x < 1 / 2 :=
        nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
      refine (hev.mono fun x hx => ?_).frequently
      rw [complexMGF_ofReal, complexMGF_ofReal, hμ, mgf_id_map_sq_stdGaussian,
        ← mgf_gammaMeasure_half_half_eq_sqrt hx, chiSquareMeasure]
      norm_num
    rw [frequently_iff_seq_forall] at h_real ⊢
    obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
    refine ⟨fun n => xs n, ?_, fun n => ?_⟩
    · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
      constructor
      · rw [Complex.ofReal_zero.symm, Filter.tendsto_ofReal_iff]
        exact hx_tendsto.1
      · simpa using hx_tendsto.2
    · exact hx_eq n
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  exact heq (by simp [hS])

/-- Chi-square MGFs multiply by adding degrees, below `1/2`. Requires a
nonempty index set so the summed degree stays positive. -/
theorem prod_mgf_chiSquareMeasure_eq_mgf_sum {ι : Type*} {s : Finset ι}
    {p : ι → ℕ} (hs : s.Nonempty) (hp : ∀ i ∈ s, 0 < p i) {t : ℝ}
    (ht : t < 1 / 2) :
    ∏ i ∈ s, mgf id (chiSquareMeasure (p i)) t
      = mgf id (chiSquareMeasure (∑ i ∈ s, p i)) t := by
  have hb : 0 < (1 / 2 : ℝ) / (1 / 2 - t) := by
    apply div_pos (by norm_num)
    linarith
  have hterm : ∀ i ∈ s, mgf id (chiSquareMeasure (p i)) t
      = ((1 / 2 : ℝ) / (1 / 2 - t)) ^ ((p i : ℝ) / 2) := by
    intro i hi
    exact mgf_chiSquareMeasure_of_lt (hp i hi) ht
  rw [Finset.prod_congr rfl hterm]
  obtain ⟨i0, hi0⟩ := hs
  have hsum : 0 < ∑ i ∈ s, p i :=
    lt_of_lt_of_le (hp i0 hi0)
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi0)
  have hMGF := mgf_chiSquareMeasure_of_lt hsum ht
  rw [hMGF]
  have hcast : ((∑ i ∈ s, p i : ℕ) : ℝ) / 2 = ∑ i ∈ s, ((p i : ℝ) / 2) := by
    rw [Nat.cast_sum]
    rw [Finset.sum_div]
  rw [hcast, Real.rpow_sum_of_pos hb _ s]

end

end

end ProbabilityTheory
