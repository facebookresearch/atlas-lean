/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.NumericalRangeSpectrum

namespace MathlibExtTest.Analysis.InnerProductSpace.NumericalRangeSpectrum

open MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorffWanted
open MathlibExt.Analysis.InnerProductSpace.NumericalRangeSpectrum
open scoped _root_.InnerProductSpace

/-- The scalar operator `I • 1` on `ℂ` has numerical range `{-I}`: every unit
vector gives `⟪I • x, x⟫ = -I`. This pins the conjugation convention. -/
example : numericalRange ((Complex.I : ℂ) • (1 : ℂ →L[ℂ] ℂ)) = {-Complex.I} := by
  ext c
  constructor
  · rintro ⟨x, hx, hxc⟩
    rw [← hxc]
    rw [smul_apply, one_apply_eq_self, inner_smul_left, inner_self_eq_norm_sq_to_K, hx]
    simp
  · rintro rfl
    exact ⟨1, by simp, by
      rw [smul_apply, one_apply_eq_self, inner_smul_left, inner_self_eq_norm_sq_to_K]
      simp⟩

/-- But its spectrum is `{I}`: the naive unconjugated inclusion
`spectrum ⊆ closure (numericalRange)` is false, while the conjugated one holds. -/
example : (Complex.I : ℂ) ∈ spectrum ℂ ((Complex.I : ℂ) • (1 : ℂ →L[ℂ] ℂ)) := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
  simp

/-- The main theorem on the scalar operator: `conj I = -I` is in the closure
of the numerical range. -/
example : (starRingEnd ℂ) (Complex.I : ℂ)
    ∈ closure (numericalRange ((Complex.I : ℂ) • (1 : ℂ →L[ℂ] ℂ))) :=
  conj_mem_closure_numericalRange_of_mem_spectrum (by
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
    simp)

/-- The zero operator: spectrum `{0}` and numerical range `{0}`. -/
example : spectrum ℂ (0 : ℂ →L[ℂ] ℂ)
    ⊆ (starRingEnd ℂ) '' closure (numericalRange (0 : ℂ →L[ℂ] ℂ)) :=
  spectrum_subset_star_image_closure_numericalRange _

/-- An eigenvalue of the identity operator: `1` has `conj 1 = 1` in the
numerical range, witnessed by any unit vector. -/
example : (starRingEnd ℂ) (1 : ℂ)
    ∈ numericalRange (1 : ℂ →L[ℂ] ℂ) :=
  conj_mem_numericalRange_of_exists_unit_eigenvector ⟨1, by simp, by simp⟩

/-- The numerical range of the identity is contained in the unit disc. -/
example : numericalRange (1 : ℂ →L[ℂ] ℂ) ⊆ Metric.closedBall 0 ‖(1 : ℂ →L[ℂ] ℂ)‖ :=
  numericalRange_subset_closedBall_norm _

end MathlibExtTest.Analysis.InnerProductSpace.NumericalRangeSpectrum
