/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.NormalApproximateSpectrum

import Mathlib.Tactic.NormNum

/-!
# Tests for the approximate point spectrum of normal operators

Scalar operators on `ℂ` (which are normal, and self-adjoint when the scalar
is real) exercise every theorem in
`MathlibExt.Analysis.InnerProductSpace.NormalApproximateSpectrum`:

* every scalar `μ` is an approximate eigenvalue of `μ • 1`, and no other
  scalar is, so the spectrum of `μ • 1` is exactly `{μ}`;
* the zero operator has `0` as an approximate eigenvalue, both directly and
  via its exact eigenvalue;
* `2 • 1` has dense range, from its trivial kernel and normality;
* the self-adjoint specialization recovers `2 ∈ spectrum ℂ (2 • 1)`.
-/

namespace MathlibExtTest.Analysis.InnerProductSpace.NormalApproximateSpectrumTests

open MathlibExt.Analysis.InnerProductSpace.NormalApproximateSpectrum

/-- A scalar operator is normal (it is `μ • 1 - 0` with `0` normal). -/
theorem isStarNormal_smul_one_complex (μ : ℂ) :
    IsStarNormal (μ • (1 : ℂ →L[ℂ] ℂ)) := by
  have h0 : IsStarNormal (0 : ℂ →L[ℂ] ℂ) := by
    simp [isStarNormal_iff]
  have h := isStarNormal_smul_one_sub (0 : ℂ →L[ℂ] ℂ) h0 μ
  simpa using h

/-- Every scalar is an approximate eigenvalue of the corresponding scalar
operator. -/
theorem isApproximateEigenvalue_smul_one_self (μ : ℂ) :
    IsApproximateEigenvalue (μ • (1 : ℂ →L[ℂ] ℂ)) μ := by
  rw [isApproximateEigenvalue_iff_forall_eps]
  intro ε hε
  refine ⟨1, by simp, ?_⟩
  have hzero : (μ • (1 : ℂ →L[ℂ] ℂ) - μ • (1 : ℂ →L[ℂ] ℂ)) (1 : ℂ) = 0 := by
    simp
  rw [hzero, norm_zero]
  exact hε

/-- No other scalar is an approximate eigenvalue of a scalar operator: the
residual on a unit vector is exactly `‖ν - μ‖`. -/
theorem not_isApproximateEigenvalue_smul_one_of_ne {μ ν : ℂ} (hν : ν ≠ μ) :
    ¬ IsApproximateEigenvalue (μ • (1 : ℂ →L[ℂ] ℂ)) ν := by
  rw [isApproximateEigenvalue_iff_forall_eps]
  intro h
  obtain ⟨x, hxnorm, hxbound⟩ :=
    h ‖ν - μ‖ (norm_pos_iff.mpr (sub_ne_zero.mpr hν))
  have hcalc : (ν • (1 : ℂ →L[ℂ] ℂ) - μ • (1 : ℂ →L[ℂ] ℂ)) x = (ν - μ) • x := by
    rw [sub_apply, smul_apply, smul_apply, one_apply_eq_self, ← sub_smul]
  rw [hcalc, norm_smul, hxnorm, mul_one] at hxbound
  exact lt_irrefl _ hxbound

/-- The spectrum of a scalar operator is the singleton of its scalar. -/
theorem mem_spectrum_smul_one_iff {μ ν : ℂ} :
    ν ∈ spectrum ℂ (μ • (1 : ℂ →L[ℂ] ℂ)) ↔ ν = μ := by
  rw [mem_spectrum_iff_isApproximateEigenvalue (isStarNormal_smul_one_complex μ)]
  exact ⟨fun h => by
    by_contra hne
    exact not_isApproximateEigenvalue_smul_one_of_ne hne h,
    fun h => h ▸ isApproximateEigenvalue_smul_one_self μ⟩

/-- `0` is an approximate eigenvalue of the zero operator. -/
theorem isApproximateEigenvalue_zero :
    IsApproximateEigenvalue (0 : ℂ →L[ℂ] ℂ) 0 := by
  have h := isApproximateEigenvalue_smul_one_self (μ := (0 : ℂ))
  have h0 : ((0 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) = 0 := by
    ext
    simp
  rw [h0] at h
  exact h

/-- `1` is not an approximate eigenvalue of the zero operator. -/
theorem not_isApproximateEigenvalue_zero_one :
    ¬ IsApproximateEigenvalue (0 : ℂ →L[ℂ] ℂ) 1 := by
  have h := not_isApproximateEigenvalue_smul_one_of_ne (μ := (0 : ℂ)) (ν := 1)
    (by norm_num)
  have h0 : ((0 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) = 0 := by
    ext
    simp
  rw [h0] at h
  exact h

/-- `0` is an exact eigenvalue of the zero operator, hence an approximate
eigenvalue. -/
theorem isApproximateEigenvalue_of_hasEigenvalue_zero :
    IsApproximateEigenvalue (0 : ℂ →L[ℂ] ℂ) 0 := by
  apply isApproximateEigenvalue_of_hasEigenvalue
  rw [Module.End.hasEigenvalue_iff]
  have heig : Module.End.eigenspace (0 : ℂ →L[ℂ] ℂ).toLinearMap 0 = ⊤ := by
    ext
    simp
  rw [heig]
  exact top_ne_bot

/-- `2 • 1` has dense range: it is normal with trivial kernel. -/
theorem denseRange_two_smul :
    DenseRange (((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) : ℂ → ℂ) :=
  denseRange_of_isStarNormal_of_ker_eq_bot (isStarNormal_smul_one_complex 2) (by
    ext
    simp)

/-- The self-adjoint specialization: `2` is in the spectrum of `2 • 1`. -/
theorem mem_spectrum_two_smul_selfAdjoint :
    (2 : ℂ) ∈ spectrum ℂ ((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) := by
  have hsa : IsSelfAdjoint ((2 : ℂ) • (1 : ℂ →L[ℂ] ℂ)) := by
    simp [IsSelfAdjoint]
  exact (mem_spectrum_iff_isApproximateEigenvalue_of_isSelfAdjoint hsa).mpr
    (isApproximateEigenvalue_smul_one_self 2)

end MathlibExtTest.Analysis.InnerProductSpace.NormalApproximateSpectrumTests
