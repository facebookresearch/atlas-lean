/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.SelfAdjointPositiveSpectrum
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Tests for positivity iff spectrum nonnegative

On `ℝ →L[ℝ] ℝ`, checked against scalar operators, where the spectrum
can be computed directly:

* The identity operator is positive, so its spectrum is nonnegative
  (forward direction of `positive_iff_spectrum_nonneg`).
* The scalar operator `2 • 1` is positive via the spectrum side
  (reverse direction), using `spectrum (2 • 1) = {2}`.
* The scalar operator `-1 • 1` is not positive: `-1` is in its spectrum
  with real part `-1` (forward direction, contrapositive).
* The forward lemma `spectrum_re_nonneg_of_reApplyInnerSelf_nonneg`,
  applied to `3 • 1`, whose `reApplyInnerSelf` is `3 * ‖u‖² ≥ 0`.
-/

open MathlibExt.Analysis.InnerProductSpace.SelfAdjointPositiveSpectrum
open ContinuousLinearMap
open scoped InnerProductSpace

namespace MathlibExtTest.Analysis.InnerProductSpace.SelfAdjointPositiveSpectrumTests

/-- The identity operator on `ℝ` is positive, so its spectrum is nonnegative. -/
example : ∀ μ ∈ spectrum ℝ (1 : ℝ →L[ℝ] ℝ), 0 ≤ RCLike.re μ := by
  apply (positive_iff_spectrum_nonneg (1 : ℝ →L[ℝ] ℝ) (IsSelfAdjoint.one _)).mp
  intro u
  simp [ContinuousLinearMap.reApplyInnerSelf_apply]
  positivity

/-- The spectrum of the scalar operator `2 • 1` on `ℝ` is `{2}`. -/
example : spectrum ℝ ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (2 : ℝ)) = {2} := by
  ext μ
  simp

/-- The scalar operator `2 • 1` on `ℝ` is positive, via the spectrum side. -/
example : ∀ u : ℝ, 0 ≤ ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (2 : ℝ)).reApplyInnerSelf u := by
  apply (positive_iff_spectrum_nonneg ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (2 : ℝ))
    (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all 2))).mpr
  intro μ hμ
  have hspec : spectrum ℝ ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (2 : ℝ)) = {2} := by
    ext ν
    simp
  rw [hspec] at hμ
  rw [Set.mem_singleton_iff] at hμ
  rw [hμ]
  simp

/-- `-1` is in the spectrum of the scalar operator `-1 • 1` on `ℝ`. -/
example : (-1 : ℝ) ∈ spectrum ℝ ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (-1 : ℝ)) := by
  rw [spectrum.mem_iff]
  simp

/-- The scalar operator `-1 • 1` on `ℝ` is not positive. -/
example : ¬ ∀ u : ℝ, 0 ≤ ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (-1 : ℝ)).reApplyInnerSelf u := by
  intro hpos
  have hspec := (positive_iff_spectrum_nonneg ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (-1 : ℝ))
    (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all (-1)))).mp hpos
  have hmem : (-1 : ℝ) ∈ spectrum ℝ ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (-1 : ℝ)) := by
    rw [spectrum.mem_iff]
    simp
  have := hspec _ hmem
  have hle : (0 : ℝ) ≤ (-1 : ℝ) := this
  linarith

/-- The forward lemma, applied to the scalar operator `3 • 1` on `ℝ`. -/
example : ∀ μ ∈ spectrum ℝ ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (3 : ℝ)), 0 ≤ RCLike.re μ := by
  apply spectrum_re_nonneg_of_reApplyInnerSelf_nonneg
  intro u
  have h : ((algebraMap ℝ (ℝ →L[ℝ] ℝ)) (3 : ℝ)).reApplyInnerSelf u = 3 * ‖u‖ ^ 2 := by
    simp [ContinuousLinearMap.reApplyInnerSelf_apply, ContinuousLinearMap.algebraMap_apply]
    ring
  rw [h]
  positivity

end MathlibExtTest.Analysis.InnerProductSpace.SelfAdjointPositiveSpectrumTests
