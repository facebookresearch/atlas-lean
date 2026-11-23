/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Eigenvectors of an inverse matrix -/

@[expose] public section

namespace Matrix

/-- **Eigenvalues of the inverse matrix.** An invertible matrix and its inverse have the same
eigenvectors with reciprocal nonzero eigenvalues. -/
theorem hasEigenvector_toLin'_inv_iff {n : Type*} [DecidableEq n] [Fintype n]
    {K : Type*} [Field K] (M : Matrix n n K) (hM : IsUnit M.det) {μ : K}
    (hμ : μ ≠ 0) (x : n → K) :
    Module.End.HasEigenvector (toLin' M) μ x ↔
      Module.End.HasEigenvector (toLin' M⁻¹) μ⁻¹ x := by
  simp only [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, toLin'_apply]
  have reciprocal (A B : Matrix n n K) (hBA : B * A = 1) {a : K} (ha : a ≠ 0)
      (h : A *ᵥ x = a • x) : B *ᵥ x = a⁻¹ • x := by
    have hscaled : a • (B *ᵥ x) = x := calc
      a • (B *ᵥ x) = B *ᵥ (a • x) := (mulVec_smul B a x).symm
      _ = B *ᵥ (A *ᵥ x) := by rw [h]
      _ = x := by rw [mulVec_mulVec, hBA, one_mulVec]
    calc
      B *ᵥ x = (a⁻¹ * a) • (B *ᵥ x) := by rw [inv_mul_cancel₀ ha, one_smul]
      _ = a⁻¹ • x := by rw [mul_smul, hscaled]
  constructor
  · rintro ⟨h, hx⟩
    exact ⟨reciprocal M M⁻¹ (M.nonsing_inv_mul hM) hμ h, hx⟩
  · rintro ⟨h, hx⟩
    refine ⟨?_, hx⟩
    simpa only [inv_inv] using reciprocal M⁻¹ M (M.mul_nonsing_inv hM) (inv_ne_zero hμ) h

end Matrix
