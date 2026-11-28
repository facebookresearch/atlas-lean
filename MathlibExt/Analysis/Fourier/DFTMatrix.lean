/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.QuantumInformation.Finite.QuantumFourierTransform

/-!
# Normalized discrete Fourier matrices with both signs

For `d∈ℕ`, an integer `s`, and zero-based indices `i,j∈Fin d`, the entry is
`exp(2π I s i j/d)/√d`. The positive and negative signs use the canonical quantum Fourier
matrix and its adjoint. Other integer signs retain the same exponential formula.

Both signs are unitary for every natural dimension, including the unique empty matrix at
`d=0`. The normalization and complex coordinate convention are the canonical ones of
`qftMatrix`; no separate orthogonality proof or matrix norm is introduced here.
-/

@[expose] public section

open Complex Matrix
open scoped Matrix ComplexConjugate
open MathlibExt.QuantumInformation.Finite.QuantumFourierTransform

namespace Matrix

/-- **Normalized Fourier matrix with an integer exponent sign.** For `d∈ℕ` and `s∈ℤ`, this
is the complex `d×d` matrix with entry `exp(2π I s i j/d)/√d`. Its `s=1` branch is the
canonical `qftMatrix d`, and its `s=-1` branch is its adjoint. Other integer signs keep
that same exponential entry formula. At `d=0` the matrix is the unique empty matrix. -/
noncomputable def dftMatrix (d : ℕ) (s : ℤ) : Matrix (Fin d) (Fin d) ℂ :=
  if s = 1 then qftMatrix d else
    if s = -1 then star (qftMatrix d) else
      Matrix.of fun i j =>
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
          (i.val : ℂ) * (j.val : ℂ) / (d : ℂ)) /
          (Real.sqrt (d : ℝ) : ℂ)

private theorem dftMatrix_pos (d : ℕ) : dftMatrix d 1 = qftMatrix d := by
  simp only [dftMatrix, ite_true]

private theorem dftMatrix_neg (d : ℕ) : dftMatrix d (-1) = star (qftMatrix d) := by
  simp [dftMatrix]

private theorem qftMatrix_star_apply (d : ℕ) (i j : Fin d) :
    star (qftMatrix d) i j =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-1 : ℤ) : ℂ) *
        (i.val : ℂ) * (j.val : ℂ) / (d : ℂ)) /
        (Real.sqrt (d : ℝ) : ℂ) := by
  have hsymm : qftMatrix d j i = qftMatrix d i j :=
    congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) (qftMatrix_transpose d)
  rw [Matrix.star_apply, hsymm, qftMatrix_apply]
  change (starRingEnd ℂ)
      (((Real.sqrt (d : ℝ) : ℂ)⁻¹) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (i.val : ℂ) * (j.val : ℂ) / (d : ℂ))) = _
  rw [map_mul, map_inv₀, conj_ofReal, ← exp_conj]
  have harg : (starRingEnd ℂ)
      (2 * (Real.pi : ℂ) * Complex.I * (i.val : ℂ) * (j.val : ℂ) / (d : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I * ((-1 : ℤ) : ℂ) *
        (i.val : ℂ) * (j.val : ℂ) / (d : ℂ) := by
    simp only [map_div₀, map_mul, conj_ofReal, conj_I, conj_natCast, map_ofNat,
      Int.cast_neg, Int.cast_one]
    ring
  rw [harg, div_eq_mul_inv]
  exact mul_comm _ _

/-- **Entry formula of the normalized discrete Fourier matrix.** For `d∈ℕ`, `s∈ℤ` and
zero-based `i,j∈Fin d`, `dftMatrix d s i j=exp(2π Complex.I s i.val j.val/d)/(√d : ℂ)`.
The integer sign is unrestricted; the formula agrees with both canonical unitary branches.
For `d=0` there are no indices at which an entry must be evaluated. -/
@[simp]
theorem dftMatrix_apply (d : ℕ) (s : ℤ) (i j : Fin d) :
    dftMatrix d s i j =
      Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
            (i.val : ℂ) * (j.val : ℂ) / (d : ℂ)) /
        (Real.sqrt (d : ℝ) : ℂ) := by
  by_cases hp : s = 1
  · subst s
    rw [dftMatrix_pos, qftMatrix_apply]
    simp only [Int.cast_one, mul_one, div_eq_mul_inv]
    exact mul_comm _ _
  · by_cases hn : s = -1
    · subst s
      rw [dftMatrix_neg]
      exact qftMatrix_star_apply d i j
    · have hMatrix : dftMatrix d s = Matrix.of (fun a b : Fin d =>
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ) *
            (a.val : ℂ) * (b.val : ℂ) / (d : ℂ)) /
            (Real.sqrt (d : ℝ) : ℂ)) := by
        simp only [dftMatrix, ite_eq_right hp, ite_eq_right hn]
      exact congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) hMatrix

/-- **Positive-sign normalized Fourier unitary.** For every `d∈ℕ`, `dftUnitaryPos d` is the
canonical unitary complex Fourier matrix, with entries `exp(2π I i j/d)/√d`. Its
unitarity is inherited from `qftMatrix_mem_unitaryGroup`. The dimension may be zero. -/
noncomputable def dftUnitaryPos (d : ℕ) : Matrix.unitaryGroup (Fin d) ℂ where
  val := dftMatrix d 1
  property := by
    rw [dftMatrix_pos]
    exact qftMatrix_mem_unitaryGroup d

/-- **Negative-sign normalized Fourier unitary.** For every `d∈ℕ`, `dftUnitaryNeg d` is the
adjoint of the canonical Fourier unitary, with entries `exp(-2π I i j/d)/√d`.
Unitarity follows by taking the star of a unitary matrix. The dimension may be zero. -/
noncomputable def dftUnitaryNeg (d : ℕ) : Matrix.unitaryGroup (Fin d) ℂ where
  val := dftMatrix d (-1)
  property := by
    rw [dftMatrix_neg]
    exact Unitary.star_mem (qftMatrix_mem_unitaryGroup d)

/-- **Underlying matrix of the positive Fourier unitary.** For every natural dimension `d`,
the matrix underlying `dftUnitaryPos d` is `dftMatrix d 1`, including the empty matrix
when `d=0`. -/
@[simp]
theorem dftUnitaryPos_val (d : ℕ) :
    (dftUnitaryPos d : Matrix (Fin d) (Fin d) ℂ) = dftMatrix d 1 :=
  rfl

/-- **Underlying matrix of the negative Fourier unitary.** For every natural dimension `d`,
the matrix underlying `dftUnitaryNeg d` is `dftMatrix d (-1)`, including the empty matrix
when `d=0`. -/
@[simp]
theorem dftUnitaryNeg_val (d : ℕ) :
    (dftUnitaryNeg d : Matrix (Fin d) (Fin d) ℂ) = dftMatrix d (-1) :=
  rfl

end Matrix
