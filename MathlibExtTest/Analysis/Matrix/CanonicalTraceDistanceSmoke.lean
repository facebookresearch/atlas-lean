/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Analysis.Matrix.TraceDistance
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
# Canonical trace norm and half trace distance on a singular matrix

The positive semidefinite complex matrix `diag(2,0)` has canonical trace
norm two. Its full trace distance from zero is two, and its half-normalized
trace distance is one. Scaling by `3i` gives trace norm and full distance six
and half distance three. The singular-value bridge computes the same norm,
and zero scaling and an empty matrix retain zero distance.
-/

noncomputable section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace MathlibExtTest.CanonicalTraceDistance

private def diagonalMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = 0 then 2 else 0)

private theorem diagonal_posSemidef : diagonalMatrix.PosSemidef := by
  rw [diagonalMatrix, Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

private theorem diagonal_traceNorm : diagonalMatrix.traceNorm = 2 := by
  have htrace : diagonalMatrix.traceNorm = RCLike.re diagonalMatrix.trace := by
    simpa only [RCLike.ofReal_re] using
      congrArg (RCLike.re : ℂ → ℝ) diagonal_posSemidef.traceNorm_eq_trace
  rw [htrace]
  norm_num [diagonalMatrix, Matrix.trace, Fin.sum_univ_two]

example : diagonalMatrix.traceNorm = 2 ∧ diagonalMatrix ≠ 0 := by
  refine ⟨diagonal_traceNorm, ?_⟩
  intro h
  have ht := diagonal_traceNorm
  rw [h, Matrix.traceNorm_zero] at ht
  norm_num at ht

example :
    Matrix.traceNormDist diagonalMatrix 0 = 2 ∧
      Matrix.traceDist diagonalMatrix 0 = 1 := by
  rw [Matrix.traceNormDist_def, Matrix.traceDist_def, sub_zero, diagonal_traceNorm]
  norm_num

example :
    ((3 * Complex.I) • diagonalMatrix).traceNorm = 6 ∧
      Matrix.traceNormDist ((3 * Complex.I) • diagonalMatrix) 0 = 6 ∧
      Matrix.traceDist ((3 * Complex.I) • diagonalMatrix) 0 = 3 := by
  rw [Matrix.traceNormDist_def, Matrix.traceDist_def, sub_zero,
    Matrix.traceNorm_smul diagonalMatrix (3 * Complex.I), diagonal_traceNorm]
  norm_num [norm_mul]

example :
    ∑ i ∈ Finset.range (Fintype.card (Fin 2)),
      diagonalMatrix.toEuclideanLin.singularValues i = 2 := by
  have h := Matrix.traceNorm_eq_sum_linearMap_singularValues diagonalMatrix
  rw [diagonal_traceNorm] at h
  exact h.symm

example :
    Matrix.traceDist 0 diagonalMatrix = 1 ∧
      Matrix.traceDist diagonalMatrix diagonalMatrix = 0 := by
  rw [Matrix.traceDist_comm 0 diagonalMatrix, Matrix.traceDist_self,
    Matrix.traceDist_def, sub_zero, diagonal_traceNorm]
  norm_num

example :
    ((0 : ℂ) • diagonalMatrix).traceNorm = 0 ∧
      Matrix.traceDist (0 : Matrix (Fin 0) (Fin 0) ℂ) 0 = 0 := by
  simp

private def secondDiagonal : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i = 0 then 3 else 1)

private theorem difference_eq_one : secondDiagonal - diagonalMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [secondDiagonal, diagonalMatrix, Matrix.diagonal]

private theorem two_distinct_nonzero :
    secondDiagonal ≠ 0 ∧ diagonalMatrix ≠ 0 ∧ secondDiagonal ≠ diagonalMatrix := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) h
    norm_num [secondDiagonal, Matrix.diagonal] at hentry
  · intro h
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    norm_num [diagonalMatrix, Matrix.diagonal] at hentry
  · intro h
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) h
    norm_num [secondDiagonal, diagonalMatrix, Matrix.diagonal] at hentry

private theorem identity_traceNorm : (1 : Matrix (Fin 2) (Fin 2) ℂ).traceNorm = 2 := by
  have h := congrArg (RCLike.re : ℂ → ℝ)
    (Matrix.PosSemidef.one (n := Fin 2) (R := ℂ)).traceNorm_eq_trace
  simpa [Matrix.trace, Fin.sum_univ_two] using h

example :
    Matrix.traceNormDist secondDiagonal diagonalMatrix = 2 ∧
      Matrix.traceDist secondDiagonal diagonalMatrix = 1 ∧
        secondDiagonal ≠ 0 ∧ diagonalMatrix ≠ 0 ∧ secondDiagonal ≠ diagonalMatrix := by
  rw [Matrix.traceNormDist_def, Matrix.traceDist_def, difference_eq_one, identity_traceNorm]
  norm_num
  exact two_distinct_nonzero

example :
    Matrix.traceDist ((Complex.I) • secondDiagonal) ((Complex.I) • diagonalMatrix) = 1 := by
  rw [Matrix.traceDist_def, ← smul_sub, difference_eq_one, Matrix.traceNorm_smul,
    identity_traceNorm]
  norm_num

end MathlibExtTest.CanonicalTraceDistance
