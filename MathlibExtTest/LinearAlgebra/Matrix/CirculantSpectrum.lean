/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.CirculantSpectrum

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for circulant spectra

Concrete checks at `n = 2` for the shift circulant matrix `[[0, 1], [1, 0]]`:
its Fourier eigenvalues are `1` and `-1`, its determinant is `-1`, and its
eigenvalues sum to `0`.
-/

@[expose] public section

namespace MathlibExt.LinearAlgebra.Matrix.CirculantSpectrumTest

open MathlibExt.LinearAlgebra.Matrix.CirculantSpectrum

private lemma sum_zmod_two (f : ZMod 2 → ℂ) : ∑ k, f k = f 0 + f 1 := by
  have h : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [h, Finset.sum_insert (by decide), Finset.sum_singleton]

private lemma prod_zmod_two (f : ZMod 2 → ℂ) : ∏ k, f k = f 0 * f 1 := by
  have h : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [h, Finset.prod_insert (by decide), Finset.prod_singleton]

/-- The shift vector on `ZMod 2`: `v 0 = 0`, `v 1 = 1`. -/
private def shiftVec : ZMod 2 → ℂ := fun k => if k = 1 then 1 else 0

private lemma shiftVec_zero : shiftVec 0 = 0 := by simp [shiftVec]

private lemma shiftVec_one : shiftVec 1 = 1 := by simp [shiftVec]

private lemma zeta_two : zeta 2 = -1 := by
  have h : (2 * Real.pi * Complex.I / ((2 : ℕ) : ℂ)) = Real.pi * Complex.I := by
    rw [show (2 * Real.pi * Complex.I) = (Real.pi * Complex.I) * ((2 : ℕ) : ℂ) by
        push_cast; ring,
      mul_div_cancel_right₀ _ (by norm_num)]
  unfold zeta
  rw [h]
  exact Complex.exp_pi_mul_I

/-- The circulant matrix of the shift vector is the anti-diagonal matrix. -/
example : (Matrix.circulant shiftVec) 0 1 = 1 := by
  simp only [Matrix.circulant_apply, shiftVec]
  rw [show (0 - 1 : ZMod 2) = 1 from by decide, ite_eq_left rfl]

/-- The circulant matrix of the shift vector has a zero diagonal entry. -/
example : (Matrix.circulant shiftVec) 0 0 = 0 := by
  simp only [Matrix.circulant_apply, shiftVec]
  rw [show (0 - 0 : ZMod 2) = 0 from by decide]
  simp

/-- The `j = 0` Fourier eigenvalue of the shift circulant is `1`. -/
example : circulantEigenvalue 2 shiftVec 0 = 1 := by
  rw [circulantEigenvalue_zero, sum_zmod_two, shiftVec_zero, shiftVec_one, zero_add]

/-- The `j = 1` Fourier eigenvalue of the shift circulant is `-1`. -/
example : circulantEigenvalue 2 shiftVec 1 = -1 := by
  rw [circulantEigenvalue_apply]
  rw [sum_zmod_two]
  have hval : (1 : ZMod 2).val = 1 := rfl
  rw [hval, shiftVec_zero, shiftVec_one]
  simp [zeta_two]

/-- The determinant of the shift circulant is `-1`, via the product of eigenvalues. -/
example : (Matrix.circulant shiftVec).det = -1 := by
  rw [det_circulant, prod_zmod_two]
  have h0 : circulantEigenvalue 2 shiftVec 0 = 1 := by
    rw [circulantEigenvalue_zero, sum_zmod_two, shiftVec_zero, shiftVec_one, zero_add]
  have h1 : circulantEigenvalue 2 shiftVec 1 = -1 := by
    rw [circulantEigenvalue_apply]
    rw [sum_zmod_two]
    have hval : (1 : ZMod 2).val = 1 := rfl
    rw [hval, shiftVec_zero, shiftVec_one]
    simp [zeta_two]
  rw [h0, h1, one_mul]

/-- The Fourier eigenvalues of the shift circulant sum to `0 = 2 * v 0`. -/
example : ∑ j, circulantEigenvalue 2 shiftVec j = 0 := by
  rw [sum_circulantEigenvalue, shiftVec_zero, mul_zero]

/-- The eigenvalue at `j = 0` of the constant vector is the size `n`. -/
example : circulantEigenvalue 3 (fun _ => (1 : ℂ)) 0 = 3 := by
  rw [circulantEigenvalue_zero]
  simp

/-- The exponential remains total at size zero, where it is `1`. -/
example : zeta 0 = 1 := by simp [zeta]

/-- At size one the exponential is the primitive first root, `1`. -/
example : zeta 1 = 1 := by simp [zeta]

/-- At size one the only eigenvalue is the only vector entry. -/
example (v : ZMod 1 → ℂ) : circulantEigenvalue 1 v 0 = v 0 := by
  rw [circulantEigenvalue_zero]
  simp only [Fintype.sum_unique]
  exact congrArg v (Subsingleton.elim _ _)

/-- The size-one Fourier matrix is the identity. -/
example : fourierMatrix 1 = (1 : Matrix (ZMod 1) (ZMod 1) ℂ) := by
  ext i j
  simp [fourierMatrix, fourierVec, Matrix.one_apply, Subsingleton.elim i 0,
    Subsingleton.elim j 0]

/-- The size-one inverse Fourier matrix is also the identity. -/
example : fourierMatrixInv 1 = (1 : Matrix (ZMod 1) (ZMod 1) ℂ) := by
  ext i j
  simp [fourierMatrixInv, Matrix.one_apply, Subsingleton.elim i 0, Subsingleton.elim j 0]

variable {n : ℕ} [NeZero n]

-- A client can pass the eigenvalues directly to the canonical linear-equivalence inverse.
example (v : ZMod n → ℂ) :
    ZMod.dft.symm (circulantEigenvalue n v) = v := by
  change ZMod.dft.symm (ZMod.dft v) = v
  exact ZMod.dft.symm_apply_apply v

-- The spectral transform has the canonical DFT interface definitionally.
example (v : ZMod n → ℂ) : circulantEigenvalue n v = ZMod.dft v := by rfl

-- Fourier vectors carry the canonical character, with the positive sign.
example (j i : ZMod n) : fourierVec n j i = ZMod.stdAddChar (i * j) := by rfl

-- Fourier matrix multiplication is the canonical inverse DFT up to n.
example (v : ZMod n → ℂ) :
    Matrix.mulVec (fourierMatrix n) v = (n : ℂ) • ZMod.dft.symm v := by
  exact fourierMatrix_mulVec_eq_invDFT v

example (v : ZMod n → ℂ) :
    Matrix.mulVec (fourierMatrixInv n) v = (n : ℂ)⁻¹ • ZMod.dft v := by
  exact fourierMatrixInv_mulVec_eq_dft v

/-- At the last frequency of `ZMod 3`, a shift has the negative-character eigenvalue. -/
example : circulantEigenvalue 3 (Pi.single 1 (1 : ℂ)) 2 =
    ZMod.stdAddChar (-(2 : ZMod 3)) := by
  simp [circulantEigenvalue, ZMod.dft_apply, Pi.single_apply]

/-- The zero input has zero Fourier eigenvalues at every frequency. -/
example (j : ZMod n) : circulantEigenvalue n (0 : ZMod n → ℂ) j = 0 := by
  exact congrFun (ZMod.dft.map_zero) j

end MathlibExt.LinearAlgebra.Matrix.CirculantSpectrumTest
