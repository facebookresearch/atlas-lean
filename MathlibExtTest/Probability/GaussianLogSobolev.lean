/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.GaussianLogSobolev
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Probability.Moments.Basic

@[expose] public section

/-!
# Tests for Gross' logarithmic Sobolev inequality

* The constant density `1` has zero Fisher information, so the inequality forces
  `KL(γ ‖ γ) = 0`.
* A density with `‖Df‖² ≤ C f` has finite Fisher information, and the inequality then shows that
  its relative entropy is finite, with `KL(f γ ‖ γ) ≤ C / 2`.
* For a continuous linear functional `L`, the density `exp (L x - ‖L‖² / 2)` of a shifted
  Gaussian has `∫ f dγ = 1` and Fisher information `‖L‖²`, so `KL(f γ ‖ γ) ≤ ‖L‖² / 2` (both
  sides are in fact equal). On `ℝ` this is the density `exp (x - 1/2)`, with bound `1/2`.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ContDiff
open MathlibExt.Probability.GaussianLogSobolevWanted

namespace MathlibExtTest.Probability.GaussianLogSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The constant density `1`: the right-hand side vanishes, so the inequality gives
`KL(γ ‖ γ) ≤ 0`. -/
example : klDiv ((stdGaussian E).withDensity fun _ => ENNReal.ofReal 1) (stdGaussian E) ≤ 0 := by
  have h := klDiv_withDensity_stdGaussian_le (E := E) (f := fun _ => (1 : ℝ)) contDiff_const
    (fun _ => one_pos) (by simp)
  have h0 : ∫⁻ x, ‖fderiv ℝ (fun _ : E => (1 : ℝ)) x‖ₑ ^ 2 / ENNReal.ofReal 1
      ∂stdGaussian E = 0 := by simp [← ofReal_norm]
  rwa [h0, mul_zero] at h

/-- **Finite Fisher information gives finite entropy.** If `‖Df‖² ≤ C f`, then
`KL(f γ ‖ γ) ≤ C / 2`; in particular the log-likelihood ratio is integrable. -/
theorem klDiv_le_of_norm_fderiv_sq_le {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfpos : ∀ x, 0 < f x)
    (hfint : ∫ x, f x ∂stdGaussian E = 1) {C : ℝ} (hC : ∀ x, ‖fderiv ℝ f x‖ ^ 2 ≤ C * f x) :
    klDiv ((stdGaussian E).withDensity fun x => ENNReal.ofReal (f x)) (stdGaussian E) ≤
      ENNReal.ofReal (C / 2) := by
  refine (klDiv_withDensity_stdGaussian_le hf hfpos hfint).trans ?_
  have hb : ∀ x, ‖fderiv ℝ f x‖ₑ ^ 2 / ENNReal.ofReal (f x) ≤ ENNReal.ofReal C := fun x => by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_div_of_pos (hfpos x)]
    exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ (hfpos x)).mpr (hC x))
  calc (1 / 2 : ℝ≥0∞) * ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 / ENNReal.ofReal (f x) ∂stdGaussian E
      ≤ 1 / 2 * ∫⁻ _, ENNReal.ofReal C ∂stdGaussian E := by gcongr with x; exact hb x
    _ = ENNReal.ofReal (C / 2) := by
        rw [lintegral_const, measure_univ, mul_one, div_eq_mul_inv C, mul_comm C,
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos two_pos,
          ENNReal.ofReal_ofNat, one_div]

/-- Under the hypotheses of `klDiv_le_of_norm_fderiv_sq_le`, the relative entropy is finite. -/
example {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfpos : ∀ x, 0 < f x)
    (hfint : ∫ x, f x ∂stdGaussian E = 1) {C : ℝ} (hC : ∀ x, ‖fderiv ℝ f x‖ ^ 2 ≤ C * f x) :
    klDiv ((stdGaussian E).withDensity fun x => ENNReal.ofReal (f x)) (stdGaussian E) ≠
      (∞ : ℝ≥0∞) :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (klDiv_le_of_norm_fderiv_sq_le hf hfpos hfint hC)

/-- The exponential moment `∫ exp (L x) dγ = exp (‖L‖² / 2)` of a continuous linear functional. -/
theorem integral_exp_stdGaussian (L : StrongDual ℝ E) :
    ∫ x, Real.exp (L x) ∂stdGaussian E = Real.exp (‖L‖ ^ 2 / 2) := by
  have hmap : (stdGaussian E).map L = gaussianReal 0 (‖L‖ ^ 2).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian]
  have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := (‖L‖ ^ 2).toNNReal)) 1
  rw [← hmap, mgf, integral_map L.continuous.aemeasurable (by fun_prop)] at h
  simpa [Real.coe_toNNReal _ (sq_nonneg _)] using h

/-- **The shifted Gaussian densities.** For a continuous linear functional `L`, the density
`f x = exp (L x - ‖L‖² / 2)` satisfies `KL(f γ ‖ γ) ≤ ‖L‖² / 2`. -/
theorem klDiv_withDensity_exp_le (L : StrongDual ℝ E) :
    klDiv ((stdGaussian E).withDensity fun x => ENNReal.ofReal (Real.exp (L x - ‖L‖ ^ 2 / 2)))
      (stdGaussian E) ≤ ENNReal.ofReal (‖L‖ ^ 2 / 2) := by
  set f : E → ℝ := fun x => Real.exp (L x - ‖L‖ ^ 2 / 2) with hf_def
  have hfpos : ∀ x, 0 < f x := fun x => Real.exp_pos _
  have hfint : ∫ x, f x ∂stdGaussian E = 1 := by
    simp only [hf_def, Real.exp_sub]
    rw [integral_div, integral_exp_stdGaussian, div_self (Real.exp_pos _).ne']
  have hDf : ∀ x, fderiv ℝ f x = f x • L := fun x =>
    ((L.hasFDerivAt.sub_const (‖L‖ ^ 2 / 2)).exp).fderiv
  have hfi : Integrable f (stdGaussian E) := by
    by_contra h
    rw [integral_undef h] at hfint
    exact zero_ne_one hfint
  refine (klDiv_withDensity_stdGaussian_le (by fun_prop) hfpos hfint).trans_eq ?_
  have hpt : ∀ x, ‖fderiv ℝ f x‖ₑ ^ 2 / ENNReal.ofReal (f x) =
      ENNReal.ofReal (‖L‖ ^ 2) * ENNReal.ofReal (f x) := fun x => by
    rw [hDf x, ← ofReal_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (hfpos x),
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_div_of_pos (hfpos x),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp [(hfpos x).ne']
  simp only [hpt]
  rw [lintegral_const_mul _ (f := fun x => ENNReal.ofReal (f x))
      (ENNReal.measurable_ofReal.comp (by fun_prop)),
    ← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ fun x => (hfpos x).le), hfint,
    ENNReal.ofReal_one, mul_one, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_div_of_pos two_pos, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- On `ℝ`, the density `exp (x - 1/2)` of `N(1, 1)` relative to `N(0, 1)` has relative entropy at
most `1/2`. -/
example : klDiv ((stdGaussian ℝ).withDensity fun x => ENNReal.ofReal (Real.exp (x - 1 / 2)))
    (stdGaussian ℝ) ≤ ENNReal.ofReal (1 / 2) := by
  have h := klDiv_withDensity_exp_le (E := ℝ) (ContinuousLinearMap.id ℝ ℝ)
  simpa using h

end MathlibExtTest.Probability.GaussianLogSobolev
