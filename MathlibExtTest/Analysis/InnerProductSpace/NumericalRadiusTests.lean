/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.NumericalRadius

/-!
# Tests for the numerical radius

On the one-dimensional Hilbert space `ℂ`, with `T` being multiplication
by a scalar:

* `w(0) = 0` and `w(1) = 1` (the latter also via the self-adjoint case,
  since `1` is self-adjoint with norm `1`);
* `w(i • 1) = 1`, although `i • 1` is not self-adjoint: its quadratic
  form at `1` is `⟪i, 1⟫ = -i`, of norm `1`;
* the Cartesian parts of `i • 1` have the quadratic forms predicted by
  `quadForm_cartesianRealPart` / `quadForm_cartesianImagPart` at `x = 1`: real part `0`,
  imaginary part `1` (the sign in `quadForm_cartesianImagPart` is essential
  here, since `Im ⟪i • 1, 1⟫ = Im (-i) = -1`);
* the adjoint-invariance and the `‖T‖ ≤ 2 * w(T)` bound hold for
  `i • 1`.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.InnerProductSpace.NumericalRadiusTests

open scoped _root_.InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.NumericalRadius

/-- The numerical radius of the zero operator is `0`. -/
example : numericalRadius (0 : ℂ →L[ℂ] ℂ) = 0 :=
  le_antisymm (by simpa using numericalRadius_le_norm (0 : ℂ →L[ℂ] ℂ))
    (numericalRadius_nonneg _)

/-- The numerical radius of the identity is `1`, by direct estimation
against the unit vector `1`. -/
example : numericalRadius (1 : ℂ →L[ℂ] ℂ) = 1 := by
  apply le_antisymm (by simpa using numericalRadius_le_norm (1 : ℂ →L[ℂ] ℂ))
  have h : ‖⟪(1 : ℂ →L[ℂ] ℂ) (1 : ℂ), (1 : ℂ)⟫_ℂ‖ = 1 := by simp
  rw [← h]
  exact le_numericalRadius (by norm_num)

/-- The numerical radius of the identity is `1`, via the self-adjoint
case. -/
example : numericalRadius (1 : ℂ →L[ℂ] ℂ) = 1 := by
  rw [numericalRadius_eq_norm_of_isSelfAdjoint (show IsSelfAdjoint (1 : ℂ →L[ℂ] ℂ) from
    star_one _)]
  exact norm_one

/-- The numerical radius of multiplication by `i` is `1`. -/
example : numericalRadius ((Complex.I : ℂ) • (1 : ℂ →L[ℂ] ℂ)) = 1 := by
  apply le_antisymm _ (by
    have h : ‖⟪((Complex.I : ℂ) • (1 : ℂ →L[ℂ] ℂ)) (1 : ℂ), (1 : ℂ)⟫_ℂ‖ = 1 := by
      simp [Complex.conj_I]
    rw [← h]
    exact le_numericalRadius (by norm_num))
  calc numericalRadius ((Complex.I : ℂ) • (1 : ℂ →L[ℂ] ℂ))
      ≤ ‖(Complex.I : ℂ) • (1 : ℂ →L[ℂ] ℂ)‖ := numericalRadius_le_norm _
    _ = 1 := by simp

/-- The real part of `i • 1` has quadratic form `0` at `x = 1`: `⟪i, 1⟫ = -i`
is purely imaginary. -/
example : ⟪cartesianRealPart ((Complex.I : ℂ) • (1 : ℂ →L[ℂ] ℂ)) (1 : ℂ), (1 : ℂ)⟫_ℂ = 0 := by
  rw [quadForm_cartesianRealPart]
  simp [Complex.conj_I]

/-- The imaginary part of `i • 1` has quadratic form `1` at `x = 1`: the
sign in `quadForm_cartesianImagPart` gives `-Im ⟪i, 1⟫ = -Im (-i) = 1`. -/
example : ⟪cartesianImagPart ((Complex.I : ℂ) • (1 : ℂ →L[ℂ] ℂ)) (1 : ℂ), (1 : ℂ)⟫_ℂ = 1 := by
  rw [quadForm_cartesianImagPart]
  simp [Complex.conj_I]

/-- The `‖T‖ ≤ 2 * w(T)` bound for `T = i • 1`: `1 ≤ 2`. -/
example : ‖(Complex.I : ℂ) • (1 : ℂ →L[ℂ] ℂ)‖
    ≤ 2 * numericalRadius ((Complex.I : ℂ) • (1 : ℂ →L[ℂ] ℂ)) := by
  have hw : numericalRadius ((Complex.I : ℂ) • (1 : ℂ →L[ℂ] ℂ)) = 1 := by
    apply le_antisymm _ (by
      have hq : ‖⟪((Complex.I : ℂ) • (1 : ℂ →L[ℂ] ℂ)) (1 : ℂ), (1 : ℂ)⟫_ℂ‖ = 1 := by
        simp [Complex.conj_I]
      rw [← hq]
      exact le_numericalRadius (by norm_num))
    calc numericalRadius ((Complex.I : ℂ) • (1 : ℂ →L[ℂ] ℂ))
        ≤ ‖(Complex.I : ℂ) • (1 : ℂ →L[ℂ] ℂ)‖ := numericalRadius_le_norm _
      _ = 1 := by simp
  have h := norm_le_two_mul_numericalRadius ((Complex.I : ℂ) • (1 : ℂ →L[ℂ] ℂ))
  rw [hw] at h
  rw [hw]
  exact h

/-- Adjoint-invariance for `T = i • 1`: both radii are `1`. -/
example : numericalRadius (ContinuousLinearMap.adjoint
      ((Complex.I : ℂ) • (1 : ℂ →L[ℂ] ℂ)))
    = numericalRadius ((Complex.I : ℂ) • (1 : ℂ →L[ℂ] ℂ)) :=
  numericalRadius_adjoint _

end MathlibExtTest.Analysis.InnerProductSpace.NumericalRadiusTests
