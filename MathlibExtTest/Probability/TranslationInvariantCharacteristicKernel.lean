/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.TranslationInvariantCharacteristicKernel
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Support

@[expose] public section

/-!
# Tests for characteristic translation-invariant kernels
-/

set_option autoImplicit false

open MeasureTheory RKHS
open scoped InnerProductSpace
open MathlibExt.Probability.KernelMeanEmbedding

namespace MathlibExtTest.Probability.TranslationInvariantCharacteristicKernel

open MathlibExt.Probability.TranslationInvariantCharacteristicKernelWanted

/-- The constant kernel `k ≡ 1` on `ℝ¹` is not characteristic: its spectral measure is the
Dirac mass at `0`, whose support is not all of `ℝ¹`. -/
example : ¬ IsCharacteristic
    (RKHS.OfKernel (RKHS.outerKernel ℝ (fun _ : EuclideanSpace ℝ (Fin 1) => (1 : ℝ)))) := by
  have hk : ∀ x y : EuclideanSpace ℝ (Fin 1),
      (kernelValue
        (RKHS.OfKernel (RKHS.outerKernel ℝ (fun _ : EuclideanSpace ℝ (Fin 1) => (1 : ℝ))))
        x y : ℂ) =
        ∫ ω, Complex.exp (-((⟪x - y, ω⟫_ℝ : ℝ) : ℂ) * Complex.I)
          ∂(Measure.dirac (0 : EuclideanSpace ℝ (Fin 1))) := by
    intro x y
    have h := kernel_eq_smul
      (H := RKHS.OfKernel (RKHS.outerKernel ℝ (fun _ : EuclideanSpace ℝ (Fin 1) => (1 : ℝ))))
      x y
    rw [RKHS.OfKernel.kernel_ofKernel] at h
    have h1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) h
    simp [RKHS.outerKernel_apply] at h1
    rw [integral_dirac]
    simp [← h1]
  have h := isCharacteristic_iff_support_eq_univ (d := 1) (by norm_num)
    (Measure.dirac (0 : EuclideanSpace ℝ (Fin 1))) hk
  rw [h]
  intro hcon
  have he : EuclideanSpace.single ⟨0, by norm_num⟩ (1 : ℝ) ∉
      (Measure.dirac (0 : EuclideanSpace ℝ (Fin 1))).support := by
    rw [MeasureTheory.Measure.notMem_support_iff_exists]
    refine ⟨Metric.ball (EuclideanSpace.single ⟨0, by norm_num⟩ (1 : ℝ)) (1 / 2),
      Metric.ball_mem_nhds _ (by norm_num), ?_⟩
    rw [MeasureTheory.Measure.dirac_apply' _ measurableSet_ball]
    simp [Metric.mem_ball, dist_zero_left]
    norm_num
  exact he (hcon.symm ▸ Set.mem_univ _)

end MathlibExtTest.Probability.TranslationInvariantCharacteristicKernel
