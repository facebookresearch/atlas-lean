/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/
module

public import MathlibExt.Analysis.Fourier.DFTMatrix
public import MathlibExt.QuantumInformation.Finite.QuantumFourierTransform
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Signed normalized Fourier matrices in dimension four and zero

The canonical quantum Fourier matrix has zeroth entry `1/2` and diagonal
entry `(1,1)` equal to `i/2` in dimension four. The negative Fourier sign
has the corresponding value `−i/2`. Both signed matrices are unitary;
the canonical matrix is symmetric but is not self-adjoint. The integer
sign zero retains the exponential formula. In dimension zero both bundled
Fourier unitaries exist and have the unique empty identity matrix.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Matrix
open scoped Matrix
open MathlibExt.QuantumInformation.Finite.QuantumFourierTransform

namespace CanonicalDFTSmoke

private theorem exp_quarter :
    Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
  rw [Complex.exp_ofReal_mul_I]
  simp

private theorem sqrt_dimension_four : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
  have hfour : ((4 : ℕ) : ℝ) = (2 : ℝ) ^ 2 := by norm_num
  rw [hfour]
  exact Real.sqrt_sq (by norm_num)

private theorem qft_four_diagonal : qftMatrix 4 (1 : Fin 4) 1 = Complex.I / 2 := by
  rw [qftMatrix_apply]
  have hphase :
      2 * (Real.pi : ℂ) * Complex.I * ((1 : Fin 4) : ℂ) * ((1 : Fin 4) : ℂ) / ((4 : ℕ) : ℂ) =
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    norm_num
    ring
  rw [hphase, exp_quarter, sqrt_dimension_four]
  norm_num
  ring

private theorem positive_four_diagonal :
    Matrix.dftMatrix 4 1 (1 : Fin 4) 1 = Complex.I / 2 := by
  rw [Matrix.dftMatrix_apply]
  have hphase :
      2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) *
        (((1 : Fin 4).val) : ℂ) * (((1 : Fin 4).val) : ℂ) / ((4 : ℕ) : ℂ) =
          ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    norm_num
    ring
  rw [hphase, exp_quarter, sqrt_dimension_four]
  norm_num

private theorem negative_four_diagonal :
    Matrix.dftMatrix 4 (-1) (1 : Fin 4) 1 = -Complex.I / 2 := by
  rw [Matrix.dftMatrix_apply]
  have hphase :
      2 * (Real.pi : ℂ) * Complex.I * ((-1 : ℤ) : ℂ) *
        (((1 : Fin 4).val) : ℂ) * (((1 : Fin 4).val) : ℂ) / ((4 : ℕ) : ℂ) =
          -(((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    norm_num
    ring
  rw [hphase, Complex.exp_neg, exp_quarter, sqrt_dimension_four]
  norm_num

example : qftMatrix 4 (0 : Fin 4) 0 = 1 / 2 ∧
    qftMatrix 4 (1 : Fin 4) 1 = Complex.I / 2 ∧
    (qftMatrix 4 *ᵥ Pi.single (1 : Fin 4) (1 : ℂ)) 1 = Complex.I / 2 := by
  refine ⟨?_, qft_four_diagonal, ?_⟩
  · rw [qftMatrix_apply, sqrt_dimension_four]
    norm_num
  · rw [Matrix.mulVec_single_one]
    exact qft_four_diagonal

example : Matrix.dftMatrix 4 1 (1 : Fin 4) 1 = Complex.I / 2 ∧
    Matrix.dftMatrix 4 (-1) (1 : Fin 4) 1 = -Complex.I / 2 ∧
    Matrix.dftMatrix 4 1 ≠ Matrix.dftMatrix 4 (-1) := by
  refine ⟨positive_four_diagonal, negative_four_diagonal, ?_⟩
  intro heq
  have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => (A 1 1).im) heq
  rw [positive_four_diagonal, negative_four_diagonal] at h
  norm_num at h

example :
    (Matrix.dftUnitaryPos 4 : Matrix (Fin 4) (Fin 4) ℂ) = Matrix.dftMatrix 4 1 ∧
    (Matrix.dftUnitaryNeg 4 : Matrix (Fin 4) (Fin 4) ℂ) = Matrix.dftMatrix 4 (-1) ∧
    (Matrix.dftUnitaryPos 4 : Matrix (Fin 4) (Fin 4) ℂ) *
      star (Matrix.dftUnitaryPos 4 : Matrix (Fin 4) (Fin 4) ℂ) = 1 ∧
    (Matrix.dftUnitaryNeg 4 : Matrix (Fin 4) (Fin 4) ℂ) *
      star (Matrix.dftUnitaryNeg 4 : Matrix (Fin 4) (Fin 4) ℂ) = 1 :=
  ⟨Matrix.dftUnitaryPos_val 4, Matrix.dftUnitaryNeg_val 4,
    Matrix.mem_unitaryGroup_iff.mp (Matrix.dftUnitaryPos 4).property,
    Matrix.mem_unitaryGroup_iff.mp (Matrix.dftUnitaryNeg 4).property⟩

example : (qftMatrix 4)ᵀ = qftMatrix 4 ∧ qftMatrix 4 ≠ star (qftMatrix 4) := by
  refine ⟨qftMatrix_transpose 4, ?_⟩
  intro heq
  have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => A 1 1) heq
  rw [Matrix.star_apply, qft_four_diagonal] at h
  have him := congrArg Complex.im h
  norm_num at him

example : Matrix.dftMatrix 4 0 (1 : Fin 4) 1 = 1 / 2 := by
  rw [Matrix.dftMatrix_apply, sqrt_dimension_four]
  norm_num

example (s : ℤ) : Matrix.dftMatrix 0 s = 1 ∧
    qftMatrix 0 ∈ Matrix.unitaryGroup (Fin 0) ℂ ∧
    (Matrix.dftUnitaryPos 0 : Matrix (Fin 0) (Fin 0) ℂ) = 1 ∧
    (Matrix.dftUnitaryNeg 0 : Matrix (Fin 0) (Fin 0) ℂ) = 1 :=
  ⟨Subsingleton.elim _ _, qftMatrix_mem_unitaryGroup 0,
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end CanonicalDFTSmoke
