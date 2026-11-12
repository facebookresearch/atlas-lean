/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.SLE.BrownianFiniteDimensional
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Process.Kolmogorov








open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace StatMech.SLE



theorem integral_pow_four_gaussianReal (v : NNReal) :
    ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  let f : ℝ → ℝ := fun t ↦ Real.exp ((v : ℝ) * t ^ 2 / 2)
  have h1 : deriv f = fun t ↦ (v : ℝ) * t * f t := by
    funext t
    simp only [f]
    rw [_root_.deriv_exp (by fun_prop)]
    simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id,
      Nat.cast_ofNat, DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const', zero_mul,
      deriv_fun_pow, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
    ring
  have h2 : deriv (fun t ↦ (v : ℝ) * t * f t) =
      fun t ↦ ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * f t := by
    funext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop),
      deriv_fun_mul (by fun_prop) (by fun_prop), h1]
    simp
    ring
  have h3 : deriv (fun t ↦ ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * f t) =
      fun t ↦ (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * f t := by
    funext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), h1]
    simp
    ring
  have h4 : deriv (fun t ↦
      (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * f t) =
      fun t ↦ (3 * (v : ℝ) ^ 2 + 6 * (v : ℝ) ^ 3 * t ^ 2 +
        (v : ℝ) ^ 4 * t ^ 4) * f t := by
    have hp : deriv (fun t : ℝ ↦
        3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) =
        fun t ↦ 3 * (v : ℝ) ^ 2 + 3 * (v : ℝ) ^ 3 * t ^ 2 := by
      funext t
      rw [deriv_fun_add (by fun_prop) (by fun_prop),
        deriv_fun_mul (by fun_prop) (by fun_prop),
        deriv_fun_mul (by fun_prop) (by fun_prop)]
      simp
      ring
    funext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), hp, h1]
    ring
  calc
    ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 v) =
        iteratedDeriv 4 (mgf (fun x : ℝ ↦ x) (gaussianReal 0 v)) 0 := by
          symm
          rw [iteratedDeriv_mgf_zero] <;> simp
    _ = iteratedDeriv 4 f 0 := by
      congr 2
      funext t
      rw [mgf_fun_id_gaussianReal]
      simp [f]
    _ = 3 * (v : ℝ) ^ 2 := by
      norm_num [iteratedDeriv_succ, iteratedDeriv_zero, h1, h2, h3, h4, f]



theorem integral_increment_pow_four_brownianFiniteDimensionalLaw
    (I : Finset ℝ) (s t : I) :
    ∫ x : EuclideanSpace ℝ I, (x t - x s) ^ 4 ∂(brownianFiniteDimensionalLaw I) =
      3 * |(t : ℝ) - (s : ℝ)| ^ 2 := by
  let X : EuclideanSpace ℝ I → ℝ := fun x ↦ x t - x s
  have hX := brownianFiniteDimensionalLaw_measurePreserving_increment I s t
  calc
    ∫ x : EuclideanSpace ℝ I, (x t - x s) ^ 4
        ∂(brownianFiniteDimensionalLaw I) =
        ∫ y : ℝ, y ^ 4 ∂((brownianFiniteDimensionalLaw I).map X) := by
          symm
          rw [integral_map hX.measurable.aemeasurable (by fun_prop)]
    _ = ∫ y : ℝ, y ^ 4
        ∂(gaussianReal 0 |(t : ℝ) - (s : ℝ)|.toNNReal) := by rw [hX.map_eq]
    _ = 3 * |(t : ℝ) - (s : ℝ)| ^ 2 := by
      rw [integral_pow_four_gaussianReal]
      simp



theorem integral_norm_increment_pow_four_brownianFiniteDimensionalLaw
    (I : Finset ℝ) (s t : I) :
    ∫ x : EuclideanSpace ℝ I, ‖x t - x s‖ ^ 4 ∂(brownianFiniteDimensionalLaw I) =
      3 * |(t : ℝ) - (s : ℝ)| ^ 2 := by
  calc
    ∫ x : EuclideanSpace ℝ I, ‖x t - x s‖ ^ 4
        ∂(brownianFiniteDimensionalLaw I) =
        ∫ x : EuclideanSpace ℝ I, (x t - x s) ^ 4
          ∂(brownianFiniteDimensionalLaw I) := by
            apply integral_congr_ae
            filter_upwards [] with x
            rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]
    _ = 3 * |(t : ℝ) - (s : ℝ)| ^ 2 :=
      integral_increment_pow_four_brownianFiniteDimensionalLaw I s t




theorem brownianFiniteDimensionalLaw_isKolmogorovProcess (I : Finset ℝ) :
    IsKolmogorovProcess
      (fun t : I ↦ fun x : EuclideanSpace ℝ I ↦ x t)
      (brownianFiniteDimensionalLaw I) 4 2 3 := by
  apply IsKolmogorovProcess.mk_of_secondCountableTopology
  · intro t
    fun_prop
  · intro s t
    let L : EuclideanSpace ℝ I →L[ℝ] ℝ := EuclideanSpace.proj t - EuclideanSpace.proj s
    have hmem : MemLp (fun x : EuclideanSpace ℝ I ↦ x t - x s) 4
        (brownianFiniteDimensionalLaw I) := by
      simpa [L] using
        (IsGaussian.memLp_dual (brownianFiniteDimensionalLaw I) L 4 (by simp))
    have hint : Integrable (fun x : EuclideanSpace ℝ I ↦ ‖x t - x s‖ ^ 4)
        (brownianFiniteDimensionalLaw I) :=
      hmem.integrable_norm_pow (by norm_num)
    calc
      ∫⁻ x, edist (x s) (x t) ^ (4 : ℝ) ∂(brownianFiniteDimensionalLaw I) =
          ENNReal.ofReal (∫ x, ‖x t - x s‖ ^ 4
            ∂(brownianFiniteDimensionalLaw I)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint
          (ae_of_all _ fun _ ↦ by positivity)]
        apply lintegral_congr
        intro x
        rw [edist_dist]
        simp [Real.dist_eq, Real.norm_eq_abs, abs_sub_comm]
      _ = ENNReal.ofReal (3 * |(t : ℝ) - (s : ℝ)| ^ 2) := by
        rw [integral_norm_increment_pow_four_brownianFiniteDimensionalLaw]
      _ = (3 : NNReal) * edist s t ^ (2 : ℝ) := by
        rw [edist_dist, Subtype.dist_eq, Real.dist_eq]
        simp only [abs_sub_comm, sq_abs, Nat.ofNat_nonneg, ENNReal.ofReal_mul,
          ENNReal.ofReal_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat]
        congr 1
        rw [← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
      _ ≤ (3 : NNReal) * edist s t ^ (2 : ℝ) := le_rfl
  · norm_num
  · norm_num



theorem integral_norm_increment_pow_four_brownianFiniteDimensionalPiLaw
    (I : Finset ℝ) (s t : I) :
    ∫ x : I → ℝ, ‖x t - x s‖ ^ 4 ∂(brownianFiniteDimensionalPiLaw I) =
      3 * |(t : ℝ) - (s : ℝ)| ^ 2 := by
  rw [brownianFiniteDimensionalPiLaw,
    integral_map (WithLp.measurable_ofLp 2 (I → ℝ)).aemeasurable (by fun_prop)]
  exact integral_norm_increment_pow_four_brownianFiniteDimensionalLaw I s t



theorem brownianFiniteDimensionalPiLaw_isKolmogorovProcess (I : Finset ℝ) :
    IsKolmogorovProcess
      (fun t : I ↦ fun x : I → ℝ ↦ x t)
      (brownianFiniteDimensionalPiLaw I) 4 2 3 := by
  apply IsKolmogorovProcess.mk_of_secondCountableTopology
  · intro t
    fun_prop
  · intro s t
    let L : EuclideanSpace ℝ I →L[ℝ] ℝ := EuclideanSpace.proj t - EuclideanSpace.proj s
    have hmem : MemLp (fun x : EuclideanSpace ℝ I ↦ x t - x s) 4
        (brownianFiniteDimensionalLaw I) := by
      simpa [L] using
        (IsGaussian.memLp_dual (brownianFiniteDimensionalLaw I) L 4 (by simp))
    have hintE : Integrable (fun x : EuclideanSpace ℝ I ↦ ‖x t - x s‖ ^ 4)
        (brownianFiniteDimensionalLaw I) :=
      hmem.integrable_norm_pow (by norm_num)
    have hint : Integrable (fun x : I → ℝ ↦ ‖x t - x s‖ ^ 4)
        (brownianFiniteDimensionalPiLaw I) := by
      rw [brownianFiniteDimensionalPiLaw,
        integrable_map_measure (by fun_prop)
          (WithLp.measurable_ofLp 2 (I → ℝ)).aemeasurable]
      simpa [Function.comp_def] using hintE
    calc
      ∫⁻ x, edist (x s) (x t) ^ (4 : ℝ) ∂(brownianFiniteDimensionalPiLaw I) =
          ENNReal.ofReal (∫ x, ‖x t - x s‖ ^ 4
            ∂(brownianFiniteDimensionalPiLaw I)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint
          (ae_of_all _ fun _ ↦ by positivity)]
        apply lintegral_congr
        intro x
        rw [edist_dist]
        simp [Real.dist_eq, Real.norm_eq_abs, abs_sub_comm]
      _ = ENNReal.ofReal (3 * |(t : ℝ) - (s : ℝ)| ^ 2) := by
        rw [integral_norm_increment_pow_four_brownianFiniteDimensionalPiLaw]
      _ = (3 : NNReal) * edist s t ^ (2 : ℝ) := by
        rw [edist_dist, Subtype.dist_eq, Real.dist_eq]
        simp only [abs_sub_comm, sq_abs, Nat.ofNat_nonneg, ENNReal.ofReal_mul,
          ENNReal.ofReal_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat]
        congr 1
        rw [← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
      _ ≤ (3 : NNReal) * edist s t ^ (2 : ℝ) := le_rfl
  · norm_num
  · norm_num

end StatMech.SLE
