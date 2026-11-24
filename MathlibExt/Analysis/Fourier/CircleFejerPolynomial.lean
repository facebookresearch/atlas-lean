/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.Fourier.CircleFejer
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Actual finite Fourier Fejer polynomial and its norm bound

The polynomial is the literal normalized double Fourier sum. The same value
is the integral of the actual positive normalized kernel against the actual
L-infinity boundary class. The kernel therefore gives the genuine uniform
norm bound needed for the Hardy predual annihilation proof. This module uses
only stock Lp and circle APIs, without a source Hardy or duality model.
-/

@[expose] public section
noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal InnerProductSpace
namespace MathlibExt.Analysis.Fourier

/-- Actual finite Fourier polynomial of a normalized-circle L-infinity function. -/
def circleFejerPolynomial (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (N : ℕ) : C(UnitAddCircle, ℂ) :=
  (N + 1 : ℂ)⁻¹ • ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
    fourierCoeff (f : UnitAddCircle → ℂ) ((i : ℤ) - j) • fourier ((i : ℤ) - j)

/-- The actual circle Fourier character converts argument subtraction to its literal product formula. -/
theorem circleFourier_apply_sub (n : ℤ) (x t : UnitAddCircle) :
    fourier n (x - t) = fourier n x * fourier (-n) t := by
  rw [sub_eq_add_neg, fourier_apply, zsmul_add, AddCircle.toCircle_add, _root_.Circle.coe_mul]
  have hn : n • (-t) = (-n) • t := by rw [smul_neg, neg_smul]
  rw [hn]
  rfl

/-- Literal finite Fourier expansion of the actual positive normalized Fejer kernel. -/
theorem circleFejerKernel_fourier (N : ℕ) (x : UnitAddCircle) :
    circleFejerKernel N x = (N + 1 : ℂ)⁻¹ *
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), fourier ((i : ℤ) - j) x := by
  change (N + 1 : ℂ)⁻¹ *
    (Star.star (circleDirichletPolynomial N x) * circleDirichletPolynomial N x) = _
  rw [circleDirichletPolynomial_apply]
  have hs : Star.star (∑ j ∈ Finset.range (N + 1), fourier (j : ℤ) x) =
      ∑ j ∈ Finset.range (N + 1), Star.star (fourier (j : ℤ) x) := by
    simpa only [starRingEnd_apply] using
      map_sum (starRingEnd ℂ) (fun j : ℕ => fourier (j : ℤ) x) (Finset.range (N + 1))
  rw [hs, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j hj
  apply congrArg (fun z : ℂ => (N + 1 : ℂ)⁻¹ * z)
  have hjstar : Star.star (fourier (j : ℤ) x) = fourier (-(j : ℤ)) x := by
    simpa only [RCLike.star_def] using (fourier_neg (n := (j : ℤ)) (x := x)).symm
  rw [hjstar, mul_comm, ← fourier_add, sub_eq_add_neg]

/-- Each literal kernel-Fourier term has the actual boundary integral coefficient. -/
theorem circleFourier_integral_translate
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (n : ℤ) (x : UnitAddCircle) :
    (∫ t, f t * fourier n (x - t) ∂AddCircle.haarAddCircle) =
      fourierCoeff (f : UnitAddCircle → ℂ) n * fourier n x := by
  have he : (fun t : UnitAddCircle => f t * fourier n (x - t)) =
      fun t => (fourier n x) * (fourier (-n) t • f t) := by
    funext t
    rw [circleFourier_apply_sub, smul_eq_mul]
    ring
  rw [he, integral_const_mul]
  change fourier n x * fourierCoeff (f : UnitAddCircle → ℂ) n = _
  exact mul_comm _ _

/-- The literal Fourier kernel terms are integrable for the actual boundary function. -/
theorem circleFourier_translate_integrable
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (n : ℤ) (x : UnitAddCircle) :
    Integrable (fun t => f t * fourier n (x - t)) AddCircle.haarAddCircle := by
  have hf : Integrable (f : UnitAddCircle → ℂ) AddCircle.haarAddCircle :=
    memLp_one_iff_integrable.mp ((Lp.memLp f).mono_exponent (by simp : (1 : ℝ≥0∞) ≤ ∞))
  have h := (hf.fourier_smul (-n)).const_mul (fourier n x)
  apply h.congr
  exact Filter.Eventually.of_forall (fun t => by
    change fourier n x * (fourier (-n) t • f t) = f t * fourier n (x - t)
    rw [circleFourier_apply_sub, smul_eq_mul]
    ring)

/-- The actual finite Fourier polynomial equals convolution with the genuine normalized positive kernel. -/
theorem circleFejerPolynomial_eq_integral
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (N : ℕ) (x : UnitAddCircle) :
    circleFejerPolynomial f N x =
      ∫ t, f t * circleFejerKernel N (x - t) ∂AddCircle.haarAddCircle := by
  have he : (fun t : UnitAddCircle => f t * circleFejerKernel N (x - t)) =
      (fun t : UnitAddCircle => (N + 1 : ℂ)⁻¹ •
        (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
          f t * fourier ((i : ℤ) - j) (x - t))) := by
    funext t
    rw [circleFejerKernel_fourier]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he, integral_smul]
  rw [integral_finsetSum (Finset.range (N + 1)) (fun (i : ℕ) hi =>
    integrable_finsetSum (Finset.range (N + 1))
      (fun (j : ℕ) hj => circleFourier_translate_integrable f ((i : ℤ) - (j : ℤ)) x))]
  have hInner (i : ℕ) :
      (∫ t : UnitAddCircle, ∑ j ∈ Finset.range (N + 1),
        f t * fourier ((i : ℤ) - (j : ℤ)) (x - t) ∂AddCircle.haarAddCircle) =
        ∑ j ∈ Finset.range (N + 1),
          ∫ t : UnitAddCircle, f t * fourier ((i : ℤ) - (j : ℤ)) (x - t)
            ∂AddCircle.haarAddCircle := by
    exact integral_finsetSum (Finset.range (N + 1))
      (fun (j : ℕ) hj => circleFourier_translate_integrable f ((i : ℤ) - (j : ℤ)) x)
  simp_rw [hInner, circleFourier_integral_translate]
  simp only [circleFejerPolynomial, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
    smul_eq_mul]

/-- The actual translated kernel has real unit mass, with its genuine continuity/integrability proof. -/
theorem circleFejerKernel_integral_re_sub (N : ℕ) (x : UnitAddCircle) :
    (∫ t, (circleFejerKernel N (x - t)).re ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) = 1 := by
  have hI : Integrable (fun t => circleFejerKernel N (x - t))
      (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    memLp_one_iff_integrable.mp (ContinuousMap.memLp (p := (1 : ℝ≥0∞))
      (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle)) ℂ
      (⟨fun t => circleFejerKernel N (x - t),
        (circleFejerKernel N).continuous.comp (continuous_const.sub continuous_id)⟩ : C(UnitAddCircle, ℂ)))
  have hRe := (Complex.reCLM : ℂ →L[ℝ] ℝ).integral_comp_comm hI
  simp only [Complex.reCLM_apply] at hRe
  rw [hRe, circleFejerKernel_integral_sub]
  rfl

/-- Genuine uniform Fejer norm bound on every actual normalized-circle L-infinity class. -/
theorem circleFejerPolynomial_norm_le
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (N : ℕ) :
    ‖circleFejerPolynomial f N‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le (f := circleFejerPolynomial f N) (norm_nonneg f)).mpr
  intro x
  rw [circleFejerPolynomial_eq_integral]
  have hI : Integrable (fun t => ‖f‖ * (circleFejerKernel N (x - t)).re)
      (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    (memLp_one_iff_integrable.mp (ContinuousMap.memLp (p := (1 : ℝ≥0∞))
      (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle)) ℝ
      (⟨fun t => (circleFejerKernel N (x - t)).re,
        Complex.continuous_re.comp
          ((circleFejerKernel N).continuous.comp (continuous_const.sub continuous_id))⟩ : C(UnitAddCircle,
    ℝ)))).const_mul _
  have hbound : ∀ᵐ t ∂AddCircle.haarAddCircle,
      ‖f t * circleFejerKernel N (x - t)‖ ≤ ‖f‖ * (circleFejerKernel N (x - t)).re := by
    filter_upwards [MeasureTheory.ae_le_lpNorm_exponent_top (Lp.memLp f)] with t ht
    have htf : ‖f t‖ ≤ ‖f‖ := by
      simpa only [← toReal_eLpNorm, Lp.norm_def] using ht
    rw [norm_mul, circleFejerKernel_norm]
    exact mul_le_mul_of_nonneg_right htf (circleFejerKernel_re_nonneg _ _)
  have he := norm_integral_le_of_norm_le hI hbound
  rw [integral_const_mul, circleFejerKernel_integral_re_sub, mul_one] at he
  exact he

end MathlibExt.Analysis.Fourier
