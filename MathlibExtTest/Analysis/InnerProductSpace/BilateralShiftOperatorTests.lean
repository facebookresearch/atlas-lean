/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.BilateralShiftOperator
public import MathlibExt.Analysis.InnerProductSpace.BilateralShiftSpectrum

/-!
# Tests for the bilateral shift on `ℓ²(ℤ, 𝕜)`

* The shift moves the first basis vector up one coordinate; the backward
  shift moves it down one coordinate.
* The two shifts are mutual inverses, both have operator norm `1`, and
  the shift is unitary, unlike the unilateral shift on `ℓ²(ℕ, 𝕜)`.
* The spectrum of either shift is the unit circle: it contains `1`,
  `-1`, and `I`, but not `0`, `1/2`, or `2`.
* The truncated approximate eigenvector for `μ = 1`, `N = 2`, has
  squared norm `5` and residual squared norm `2`.
-/

open Set Filter Topology Metric
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.BilateralShiftOperator
open MathlibExt.Analysis.InnerProductSpace.BilateralShiftSpectrum

namespace MathlibExtTest.Analysis.InnerProductSpace.BilateralShiftOperatorTests

/-- The shift sends `e₀` to `e₁`: coordinate `1` is `1`. -/
example : (bilateralShiftCLM (lp.single 2 0 (1 : ℂ)) : ℤ → ℂ) 1 = 1 := by
  simp [bilateralShiftCLM_apply, lp.single_apply]

/-- The shift sends `e₀` to `e₁`: coordinate `0` is `0`. -/
example : (bilateralShiftCLM (lp.single 2 0 (1 : ℂ)) : ℤ → ℂ) 0 = 0 := by
  simp [bilateralShiftCLM_apply, lp.single_apply]

/-- The shift sends `e₀` to `e₁`: coordinate `2` is `0`. -/
example : (bilateralShiftCLM (lp.single 2 0 (1 : ℂ)) : ℤ → ℂ) 2 = 0 := by
  simp [bilateralShiftCLM_apply, lp.single_apply]

/-- The backward shift sends `e₀` to `e₋₁`: coordinate `-1` is `1`. -/
example : (bilateralBackwardCLM (lp.single 2 0 (1 : ℂ)) : ℤ → ℂ) (-1) = 1 := by
  simp [bilateralBackwardCLM_apply, lp.single_apply]

/-- The backward shift sends `e₀` to `e₋₁`: coordinate `0` is `0`. -/
example : (bilateralBackwardCLM (lp.single 2 0 (1 : ℂ)) : ℤ → ℂ) 0 = 0 := by
  simp [bilateralBackwardCLM_apply, lp.single_apply]

/-- The operator norm of the shift is `1`. -/
example : ‖bilateralShiftCLM (𝕜 := ℂ)‖ = 1 :=
  norm_bilateralShiftCLM

/-- The operator norm of the backward shift is `1`. -/
example : ‖bilateralBackwardCLM (𝕜 := ℂ)‖ = 1 :=
  norm_bilateralBackwardCLM

/-- The adjoint of the shift is the backward shift. -/
example : (bilateralShiftCLM (𝕜 := ℂ))† = bilateralBackwardCLM :=
  adjoint_bilateralShiftCLM

/-- `B ∘ S = 1`. -/
example : bilateralBackwardCLM ∘L bilateralShiftCLM =
    (1 : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ)) :=
  bilateralBackward_comp_bilateralShift

/-- `S ∘ B = 1`. -/
example : bilateralShiftCLM ∘L bilateralBackwardCLM =
    (1 : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ)) :=
  bilateralShift_comp_bilateralBackward

/-- The bilateral shift is bijective, unlike the unilateral shift. -/
example : Function.Bijective (bilateralShiftCLM (𝕜 := ℂ)) :=
  bijective_bilateralShiftCLM

/-- The bilateral shift is unitary. -/
example : bilateralShiftCLM (𝕜 := ℂ) ∈ unitary (ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ)) :=
  mem_unitary_bilateralShiftCLM

/-- The bilateral shift is an isometry. -/
example : Isometry (bilateralShiftCLM (𝕜 := ℂ)) :=
  isometry_bilateralShiftCLM

/-- `1` is in the spectrum of the shift. -/
example : (1 : ℂ) ∈ spectrum ℂ (bilateralShiftCLM (𝕜 := ℂ)) := by
  rw [spectrum_bilateralShiftCLM, mem_sphere_zero_iff_norm]
  exact norm_one

/-- `-1` is in the spectrum of the shift. -/
example : (-1 : ℂ) ∈ spectrum ℂ (bilateralShiftCLM (𝕜 := ℂ)) := by
  rw [spectrum_bilateralShiftCLM, mem_sphere_zero_iff_norm]
  simp

/-- `I` is in the spectrum of the shift. -/
example : Complex.I ∈ spectrum ℂ (bilateralShiftCLM (𝕜 := ℂ)) := by
  rw [spectrum_bilateralShiftCLM, mem_sphere_zero_iff_norm]
  exact Complex.norm_I

/-- `0` is not in the spectrum of the shift. -/
example : (0 : ℂ) ∉ spectrum ℂ (bilateralShiftCLM (𝕜 := ℂ)) := by
  rw [spectrum_bilateralShiftCLM, mem_sphere_zero_iff_norm]
  simp

/-- `1 / 2` is not in the spectrum of the shift. -/
example : (1 / 2 : ℂ) ∉ spectrum ℂ (bilateralShiftCLM (𝕜 := ℂ)) := by
  rw [spectrum_bilateralShiftCLM, mem_sphere_zero_iff_norm]
  norm_num

/-- `2` is not in the spectrum of the shift. -/
example : (2 : ℂ) ∉ spectrum ℂ (bilateralShiftCLM (𝕜 := ℂ)) := by
  rw [spectrum_bilateralShiftCLM, mem_sphere_zero_iff_norm]
  norm_num

/-- The spectrum of the backward shift is the unit circle. -/
example : spectrum ℂ (bilateralBackwardCLM (𝕜 := ℂ)) = Metric.sphere 0 1 :=
  spectrum_bilateralBackwardCLM

/-- `1` is in the spectrum of the shift over `ℝ`. -/
example : (1 : ℝ) ∈ spectrum ℝ (bilateralShiftCLM (𝕜 := ℝ)) := by
  rw [spectrum_bilateralShiftCLM, mem_sphere_zero_iff_norm]
  exact norm_one

/-- The approximate eigenvector for `μ = 1`, `N = 2`, has value `1` at `0`. -/
example : (approxEigenVec (1 : ℂ) 2 : ℤ → ℂ) 0 = 1 := by
  rw [approxEigenVec_apply, approxEigenFun_of_mem (by decide)]
  simp

/-- The approximate eigenvector for `μ = 1`, `N = 2`, has value `1` at `-2`. -/
example : (approxEigenVec (1 : ℂ) 2 : ℤ → ℂ) (-2) = 1 := by
  rw [approxEigenVec_apply, approxEigenFun_of_mem (by decide)]
  simp

/-- The approximate eigenvector for `μ = 1`, `N = 2`, vanishes at `3`. -/
example : (approxEigenVec (1 : ℂ) 2 : ℤ → ℂ) 3 = 0 := by
  rw [approxEigenVec_apply, approxEigenFun_of_notMem (by decide)]

/-- The approximate eigenvector for `μ = 1`, `N = 2`, has squared norm `5`. -/
example : ‖approxEigenVec (1 : ℂ) 2‖ ^ 2 = 5 := by
  have h := norm_sq_approxEigenVec (μ := (1 : ℂ)) (by simp) 2
  norm_num at h
  exact h

/-- The residual of the approximate eigenvector for `μ = 1`, `N = 2`,
has squared norm `2`. -/
example : ‖(algebraMap ℂ (ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ)) 1 - bilateralShiftCLM (𝕜 := ℂ))
    (approxEigenVec (1 : ℂ) 2)‖ ^ 2 = 2 :=
  norm_sq_residual_approxEigenVec (μ := (1 : ℂ)) (by simp) 2

end MathlibExtTest.Analysis.InnerProductSpace.BilateralShiftOperatorTests
