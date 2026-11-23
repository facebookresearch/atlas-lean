/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.LinearAlgebra.Matrix.Circulant

import MathlibExt.Analysis.Fourier.VectorDFT
import Mathlib.Tactic.Ring

/-!
# Circulant matrices are diagonalized by the Fourier basis

A circulant matrix `Matrix.circulant v` over `ZMod n` is the convolution
operator with `v` on the finite cyclic group `ZMod n`: its `(i, j)` entry is
`v (i - j)`. For nonzero `n`, the Fourier vectors are the standard additive
characters `fourierVec n j i = ZMod.stdAddChar (i * j)`, equivalently
`zeta n ^ (i.val * j.val)` where `zeta n = exp (2 * π * I / n)`.
Their eigenvalues are the canonical discrete Fourier transform `ZMod.dft v`,
equivalently the negative-exponent sum
`circulantEigenvalue n v j = ∑ k, v k * zeta n ^ (-(k.val * j.val : ℤ))`.
Consequently the determinant of a circulant matrix is the product of its
Fourier eigenvalues, and the eigenvalues sum to `n * v 0`.

The Fourier matrix acts as `n` times `ZMod.dft.symm`, and its inverse acts as
`n⁻¹` times `ZMod.dft`. Thus matrix inversion uses the canonical Fourier
linear equivalence. The exponential bridge reuses the existing `VectorDFT` API.

This is the finite-dimensional analogue of the Fourier-series diagonalization
of convolution operators on the circle: in `IntroductionToFunctionalAnalysis`,
Fourier series (Fejér's theorem, Bessel's inequality, Parseval's identity)
play the same role for `L² ([-π, π])`, and the companion slice on Young's
convolution inequality for finite groups treats the same convolution product.
-/

@[expose] public section

namespace MathlibExt.LinearAlgebra.Matrix.CirculantSpectrum

variable {n : ℕ} [NeZero n]

/-- The exponential `exp (2 * π * I / n)`, a primitive `n`-th root for nonzero `n`.
This definition is total: at `n = 0`, it is `exp 0 = 1`. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- For nonzero `n`, `zeta n` is the canonical standard character at `1`. -/
public theorem zeta_eq_stdAddChar : zeta n = ZMod.stdAddChar (1 : ZMod n) :=
  MathlibExt.Analysis.Fourier.FastFourierTransformWanted.stdAddChar_one_eq_exp.symm

/-- For nonzero `n`, the exponential is a primitive `n`-th root of unity. -/
public theorem zeta_isPrimitiveRoot : IsPrimitiveRoot (zeta n) n := by
  rw [zeta_eq_stdAddChar]
  exact MathlibExt.Analysis.Fourier.FastFourierTransformWanted.isPrimitiveRoot_stdAddChar_one

/-- The `j`-th Fourier vector on `ZMod n`, using the canonical positive character. -/
noncomputable def fourierVec (n : ℕ) [NeZero n] (j : ZMod n) : ZMod n → ℂ :=
  fun i => ZMod.stdAddChar (i * j)

/-- The character definition of a Fourier vector agrees with its exponential formula. -/
public theorem fourierVec_apply (j i : ZMod n) :
    fourierVec n j i = zeta n ^ (i.val * j.val) := by
  rw [zeta_eq_stdAddChar, ← AddChar.mulShift_spec', AddChar.mulShift_apply,
    Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, mul_one]
  rfl

private theorem stdAddChar_neg_mul (i j : ZMod n) :
    ZMod.stdAddChar (-(i * j)) = zeta n ^ (-(i.val * j.val : ℤ)) := by
  rw [AddChar.map_neg_eq_inv,
    show ZMod.stdAddChar (i * j) = zeta n ^ (i.val * j.val) from fourierVec_apply j i,
    zpow_neg, show (i.val * j.val : ℤ) = ((i.val * j.val : ℕ) : ℤ) by push_cast; rfl,
    zpow_natCast]

/-- The `j`-th Fourier eigenvalue of a circulant matrix is its canonical DFT. -/
noncomputable def circulantEigenvalue (n : ℕ) [NeZero n] (v : ZMod n → ℂ) (j : ZMod n) : ℂ :=
  ZMod.dft v j

/-- The canonical DFT definition agrees with the original negative-exponent eigenvalue sum. -/
public theorem circulantEigenvalue_apply (v : ZMod n → ℂ) (j : ZMod n) :
    circulantEigenvalue n v j = ∑ k, v k * zeta n ^ (-(k.val * j.val : ℤ)) := by
  simp only [circulantEigenvalue, ZMod.dft_apply, smul_eq_mul, stdAddChar_neg_mul, mul_comm]

/-- Every Fourier vector is an eigenvector of every circulant matrix. -/
public theorem circulant_mulVec_fourierVec (v : ZMod n → ℂ) (j : ZMod n) :
    Matrix.mulVec (Matrix.circulant v) (fourierVec n j) =
      circulantEigenvalue n v j • fourierVec n j := by
  funext i
  simp only [Matrix.mulVec_apply_eq_sum, Matrix.circulant_apply, Pi.smul_apply, smul_eq_mul,
    fourierVec, circulantEigenvalue, ZMod.dft_apply, smul_eq_mul]
  have hreindex : ∑ i' : ZMod n, v (i - i') * ZMod.stdAddChar (i' * j) =
      ∑ k : ZMod n, v k * ZMod.stdAddChar ((i - k) * j) := by
    refine Fintype.sum_bijective (fun i' => i - i') (Equiv.subLeft i).bijective _ _ ?_
    intro i'
    rw [sub_sub_cancel]
  rw [hreindex, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [sub_mul, AddChar.map_sub_eq_div, AddChar.map_neg_eq_inv]
  ring

/-- The Fourier matrix, whose `j`-th column is the standard character `fourierVec n j`. -/
noncomputable def fourierMatrix (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  fun i j => fourierVec n j i

/-- The Fourier matrix agrees entrywise with its original exponential formula. -/
public theorem fourierMatrix_apply (i j : ZMod n) :
    fourierMatrix n i j = zeta n ^ (i.val * j.val) :=
  fourierVec_apply j i

/-- The inverse Fourier matrix, `(1 / n)` times the negative standard character. -/
noncomputable def fourierMatrixInv (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  fun i j => (n : ℂ)⁻¹ * ZMod.stdAddChar (-(i * j))

/-- The inverse Fourier matrix agrees entrywise with its original exponential formula. -/
public theorem fourierMatrixInv_apply (i j : ZMod n) :
    fourierMatrixInv n i j = (1 / (n : ℂ)) * zeta n ^ (-(i.val * j.val : ℤ)) := by
  rw [fourierMatrixInv, stdAddChar_neg_mul, one_div]

/-- Fourier matrix multiplication is the canonical inverse DFT multiplied by `n`. -/
public theorem fourierMatrix_mulVec_eq_invDFT (v : ZMod n → ℂ) :
    Matrix.mulVec (fourierMatrix n) v = (n : ℂ) • ZMod.dft.symm v := by
  funext i
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  simp only [Matrix.mulVec_apply_eq_sum, fourierMatrix, fourierVec, Pi.smul_apply,
    ZMod.invDFT_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  simp only [mul_comm i]

/-- Inverse Fourier matrix multiplication is the canonical DFT divided by `n`. -/
public theorem fourierMatrixInv_mulVec_eq_dft (v : ZMod n → ℂ) :
    Matrix.mulVec (fourierMatrixInv n) v = (n : ℂ)⁻¹ • ZMod.dft v := by
  funext i
  simp only [Matrix.mulVec_apply_eq_sum, fourierMatrixInv, Pi.smul_apply,
    ZMod.dft_apply, smul_eq_mul, Finset.mul_sum, mul_comm i, mul_assoc]

/-- The Fourier matrix is invertible, with inverse `fourierMatrixInv`. -/
public theorem fourierMatrix_mul_inv :
    fourierMatrix n * fourierMatrixInv n = (1 : Matrix (ZMod n) (ZMod n) ℂ) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  rw [← Matrix.mulVec_mulVec, fourierMatrix_mulVec_eq_invDFT,
    fourierMatrixInv_mulVec_eq_dft, map_smul, ZMod.dft.symm_apply_apply,
    smul_smul, mul_inv_cancel₀ hn, one_smul, Matrix.one_mulVec]

/-- Circulant matrices are diagonalized by the Fourier matrix. -/
public theorem circulant_mul_fourierMatrix (v : ZMod n → ℂ) :
    Matrix.circulant v * fourierMatrix n =
      fourierMatrix n * Matrix.diagonal (circulantEigenvalue n v) := by
  funext i j
  have h := congrFun (circulant_mulVec_fourierVec (n := n) v j) i
  calc (Matrix.circulant v * fourierMatrix n) i j
      = ∑ k : ZMod n, v (i - k) * fourierVec n j k := by
        simp [Matrix.mul_apply, fourierMatrix, Matrix.circulant_apply]
    _ = circulantEigenvalue n v j * fourierVec n j i := by
        simpa [Matrix.mulVec_apply_eq_sum, Pi.smul_apply, smul_eq_mul] using h
    _ = (fourierMatrix n * Matrix.diagonal (circulantEigenvalue n v)) i j := by
        rw [Matrix.mul_apply]
        rw [Finset.sum_eq_single j
          (f := fun k => fourierMatrix n i k *
            Matrix.diagonal (circulantEigenvalue n v) k j)
          (fun k _ hk => by rw [Matrix.diagonal_apply, ite_eq_right hk, mul_zero])
          (fun hmem => absurd (Finset.mem_univ j) hmem)]
        simp only [fourierMatrix, Matrix.diagonal_apply]
        rw [ite_true, mul_comm]

/-- The determinant of a circulant matrix is the product of its Fourier eigenvalues. -/
public theorem det_circulant (v : ZMod n → ℂ) :
    (Matrix.circulant v).det = ∏ j, circulantEigenvalue n v j := by
  have hC : Matrix.circulant v =
      fourierMatrix n * Matrix.diagonal (circulantEigenvalue n v) * fourierMatrixInv n := by
    calc Matrix.circulant v = Matrix.circulant v * (fourierMatrix n * fourierMatrixInv n) := by
          rw [fourierMatrix_mul_inv, Matrix.mul_one]
      _ = (Matrix.circulant v * fourierMatrix n) * fourierMatrixInv n := by
          rw [Matrix.mul_assoc]
      _ = (fourierMatrix n * Matrix.diagonal (circulantEigenvalue n v)) * fourierMatrixInv n := by
          rw [circulant_mul_fourierMatrix]
  rw [hC, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    mul_comm (fourierMatrix n).det, mul_assoc, ← Matrix.det_mul, fourierMatrix_mul_inv,
    Matrix.det_one, mul_one]

/-- The Fourier eigenvalue at `j = 0` is the sum of the entries of `v`. -/
public theorem circulantEigenvalue_zero (v : ZMod n → ℂ) :
    circulantEigenvalue n v 0 = ∑ k, v k :=
  ZMod.dft_apply_zero v

/-- The Fourier eigenvalues sum to `n * v 0`. -/
public theorem sum_circulantEigenvalue (v : ZMod n → ℂ) :
    ∑ j, circulantEigenvalue n v j = (n : ℂ) * v 0 := by
  have h := congrFun (ZMod.dft_dft v) 0
  simpa only [ZMod.dft_apply_zero, circulantEigenvalue, neg_zero, smul_eq_mul] using h

end MathlibExt.LinearAlgebra.Matrix.CirculantSpectrum
