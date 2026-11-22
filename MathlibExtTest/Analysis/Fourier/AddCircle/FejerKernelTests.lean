/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.AddCircle.FejerTheorem
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Tests for the Fejér kernel, Cesàro–Fourier means, and Fejér's theorem

* Boundary case `N = 0`: `K₀ = 1` everywhere, so its integral, norm bound, and
  nonnegativity are all the trivial `1` case.
* The zero function has zero partial sums and zero Cesàro means, and the
  convolution identity reduces to `0 = 0`.
* Fejér's theorem applies to the constant function `1`.
* The decay estimate is exercised at the half-period point, where the first
  Fourier mode is `-1`.
-/

namespace MathlibExtTest.Analysis.Fourier.FejerKernelTests

open AddCircle Finset Filter Complex
open MeasureTheory

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The Fourier coefficients of the zero function vanish. -/
private theorem fourierCoeff_zero (n : ℤ) :
    fourierCoeff (T := T) (fun _ => (0 : ℂ)) n = 0 := by
  simp [fourierCoeff]

/-- Boundary case: `K₀ = 1`. -/
example (x : AddCircle T) : AddCircle.fejerKernel (T := T) 0 x = 1 := by
  simp [AddCircle.fejerKernel]

/-- The integral, norm bound, and nonnegativity at `N = 0`. -/
example : ∫ t : AddCircle T, AddCircle.fejerKernel (T := T) 0 t
    ∂AddCircle.haarAddCircle = 1 :=
  AddCircle.integral_fejerKernel (T := T) 0

example (x : AddCircle T) : ‖AddCircle.fejerKernel (T := T) 0 x‖ ≤ 1 := by
  simpa using AddCircle.norm_fejerKernel_le (T := T) 0 x

example (x : AddCircle T) : 0 ≤ (AddCircle.fejerKernel (T := T) 0 x).re :=
  AddCircle.fejerKernel_nonneg 0 x

/-- Symmetry and `L¹` norm at a general `N`. -/
example (N : ℕ) (x : AddCircle T) :
    AddCircle.fejerKernel (T := T) N (-x) = AddCircle.fejerKernel (T := T) N x :=
  AddCircle.fejerKernel_symmetric N x

example (N : ℕ) :
    ∫ t : AddCircle T, ‖AddCircle.fejerKernel (T := T) N t‖
      ∂AddCircle.haarAddCircle = 1 :=
  AddCircle.integral_norm_fejerKernel (T := T) N

/-- The Fejér kernel is continuous and integrable. -/
example (N : ℕ) : Continuous (AddCircle.fejerKernel (T := T) N) :=
  AddCircle.fejerKernel_continuous N

example (N : ℕ) : Integrable (AddCircle.fejerKernel (T := T) N)
    AddCircle.haarAddCircle :=
  AddCircle.fejerKernel_integrable (T := T) N

/-- The zero function has zero partial sums and zero Cesàro means. -/
example (N : ℕ) (x : AddCircle T) :
    AddCircle.partialFourierSum (T := T) (fun _ => (0 : ℂ)) N x = 0 := by
  simp [AddCircle.partialFourierSum, fourierCoeff_zero]

example (N : ℕ) (x : AddCircle T) :
    AddCircle.cesaroFourierMean (T := T) (fun _ => (0 : ℂ)) N x = 0 := by
  simp [AddCircle.cesaroFourierMean, AddCircle.partialFourierSum, fourierCoeff_zero]

/-- The convolution identity for the zero function. -/
example (N : ℕ) (x : AddCircle T) :
    AddCircle.cesaroFourierMean (T := T) (fun _ => (0 : ℂ)) N x =
    ∫ t : AddCircle T, AddCircle.fejerKernel (T := T) N t • (0 : ℂ)
      ∂AddCircle.haarAddCircle := by
  exact AddCircle.cesaroMean_eq_fejer_convolution (T := T)
    (f := fun _ => (0 : ℂ)) (integrable_zero _ _ _) N x

/-- Fejér's theorem for the constant function `1`. -/
example : TendstoUniformly
    (fun N => AddCircle.cesaroFourierMean (T := T) (⇑(1 : C(AddCircle T, ℂ))) N)
    (⇑(1 : C(AddCircle T, ℂ))) atTop :=
  AddCircle.fejer_uniform_convergence 1

/-- The half-period point has first Fourier mode `-1`. -/
example : (fourier (1 : ℤ) ((T / 2 : ℝ) : AddCircle T) : ℂ) = -1 := by
  rw [fourier_coe_apply]
  have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast hT.out.ne'
  have h : 2 * Real.pi * Complex.I * (1 : ℤ) * (T / 2 : ℝ) / T = Real.pi * Complex.I := by
    calc 2 * Real.pi * Complex.I * (1 : ℤ) * (T / 2 : ℝ) / T
        = Real.pi * Complex.I * ((T : ℂ) / T) := by push_cast; ring
      _ = Real.pi * Complex.I := by rw [div_self hTne, mul_one]
  rw [h, Complex.exp_pi_mul_I]

/-- The decay estimate at the half-period point, where `‖1 - e^{2πi x / T}‖ = 2`. -/
example (N : ℕ) :
    ‖AddCircle.fejerKernel (T := T) N ((T / 2 : ℝ) : AddCircle T)‖ ≤
      4 / (((N : ℝ) + 1) * (1 : ℝ) ^ 2) := by
  have hmode : (fourier (1 : ℤ) ((T / 2 : ℝ) : AddCircle T) : ℂ) = -1 := by
    rw [fourier_coe_apply]
    have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast hT.out.ne'
    have h : 2 * Real.pi * Complex.I * (1 : ℤ) * (T / 2 : ℝ) / T = Real.pi * Complex.I := by
      calc 2 * Real.pi * Complex.I * (1 : ℤ) * (T / 2 : ℝ) / T
          = Real.pi * Complex.I * ((T : ℂ) / T) := by push_cast; ring
        _ = Real.pi * Complex.I := by rw [div_self hTne, mul_one]
    rw [h, Complex.exp_pi_mul_I]
  have hbound := (AddCircle.fejer_kernel_properties (T := T) N).2.2.2.2 1 one_pos
    ((T / 2 : ℝ) : AddCircle T) (by rw [hmode]; norm_num)
  simpa using hbound

end MathlibExtTest.Analysis.Fourier.FejerKernelTests
