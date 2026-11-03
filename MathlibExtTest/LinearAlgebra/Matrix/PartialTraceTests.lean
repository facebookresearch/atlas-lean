/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.PartialTrace
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for partial traces of finite matrices

Concrete checks on `Fin 2 × Fin 2` matrices:

* the partial traces of an explicitly given matrix, computed entry by entry;
* the partial trace of a Kronecker product;
* the partial trace of a rank-one positive semidefinite matrix, its value
  and its positive semidefiniteness;
* the partial trace of the maximally mixed state (a density matrix);
* the trace-adjoint identity, numerically.
-/

@[expose] public section

open scoped BigOperators ComplexOrder Kronecker Matrix

open MathlibExt.LinearAlgebra.Matrix.PartialTrace

namespace MathlibExtTest.LinearAlgebra.Matrix.PartialTraceTests

/-- The test matrix: `A (i, j) (i', j') = i + 2 * j + 3 * i' + 5 * j'`. -/
private abbrev testMatrix : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  Matrix.of fun p q => (p.1 : ℝ) + 2 * (p.2 : ℝ) + 3 * (q.1 : ℝ) + 5 * (q.2 : ℝ)

/-- The partial trace of `testMatrix` over the first factor. -/
example : partialTraceLeft testMatrix = !![4, 14; 8, 18] := by
  ext j j'
  fin_cases j <;> fin_cases j' <;>
    simp [partialTraceLeft, testMatrix, Fin.sum_univ_two] <;> norm_num

/-- The partial trace of `testMatrix` over the second factor. -/
example : partialTraceRight testMatrix = !![7, 13; 9, 15] := by
  ext i i'
  fin_cases i <;> fin_cases i' <;>
    simp [partialTraceRight, testMatrix, Fin.sum_univ_two] <;> norm_num

/-- The partial trace preserves the trace of `testMatrix`. -/
example : Matrix.trace (partialTraceLeft testMatrix) = Matrix.trace testMatrix :=
  trace_partialTraceLeft testMatrix

/-- The trace of `testMatrix` is `22`. -/
example : Matrix.trace testMatrix = 22 := by
  simp [Matrix.trace, testMatrix, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

/-- The partial trace of a Kronecker product: `trace E = 5`. -/
example :
    partialTraceLeft ((!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ
        (!![5, 6; 7, 8] : Matrix (Fin 2) (Fin 2) ℝ))
      = !![25, 30; 35, 40] := by
  rw [partialTraceLeft_kronecker]
  have htr : Matrix.trace (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) = 5 := by
    norm_num [Matrix.trace, Fin.sum_univ_two]
  rw [htr]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals norm_num

/-- The partial trace of the identity is the dimension times the identity. -/
example :
    partialTraceLeft (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)
      = 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext j j'
  fin_cases j <;> fin_cases j' <;>
    simp [partialTraceLeft, Fin.sum_univ_two] <;> norm_num

/-- The partial trace of a rank-one positive semidefinite matrix, computed
explicitly from its slices. -/
example :
    partialTraceLeft (Matrix.vecMulVec
        (fun p : Fin 2 × Fin 2 => (p.1 : ℝ) + (p.2 : ℝ) + 1)
        (star fun p : Fin 2 × Fin 2 => (p.1 : ℝ) + (p.2 : ℝ) + 1))
      = !![5, 8; 8, 13] := by
  rw [partialTraceLeft_vecMulVec_star]
  simp only [Fin.sum_univ_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply] <;> norm_num

/-- The partial trace of a rank-one positive semidefinite matrix is positive
semidefinite. -/
example :
    (partialTraceLeft (Matrix.vecMulVec
        (fun p : Fin 2 × Fin 2 => (p.1 : ℝ) + (p.2 : ℝ) + 1)
        (star fun p : Fin 2 × Fin 2 => (p.1 : ℝ) + (p.2 : ℝ) + 1))).PosSemidef :=
  posSemidef_partialTraceLeft (Matrix.posSemidef_vecMulVec_self_star _)

/-- The same, over `ℂ`, with a non-real vector. -/
example :
    (partialTraceLeft (Matrix.vecMulVec
        (fun p : Fin 2 × Fin 2 => (p.1 : ℂ) + Complex.I * (p.2 : ℂ))
        (star fun p : Fin 2 × Fin 2 => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)))).PosSemidef :=
  posSemidef_partialTraceLeft (Matrix.posSemidef_vecMulVec_self_star _)

/-- The partial traces of the maximally mixed state are positive semidefinite
density matrices. -/
example :
    (partialTraceLeft ((1 / 4 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ))).PosSemidef
      ∧ Matrix.trace
          (partialTraceLeft ((1 / 4 : ℝ) •
            (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ))) = 1 := by
  have htr : Matrix.trace ((1 / 4 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ))
      = 1 := by
    rw [Matrix.trace_smul, Matrix.trace_one]
    norm_num [Fintype.card_prod, Fintype.card_fin]
  exact ⟨posSemidef_partialTraceLeft (Matrix.PosSemidef.one.smul (by norm_num)),
    trace_partialTraceLeft_of_trace_eq_one htr⟩

/-- The trace-adjoint identity on concrete matrices. -/
example :
    Matrix.trace (partialTraceLeft testMatrix * !![1, 2; 3, 4])
      = Matrix.trace (testMatrix *
          ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ !![1, 2; 3, 4])) :=
  trace_partialTraceLeft_mul testMatrix !![1, 2; 3, 4]

/-- The trace-adjoint identity, numerically: both sides equal `134`. -/
example : Matrix.trace (partialTraceLeft testMatrix * !![1, 2; 3, 4]) = 134 := by
  have hA : partialTraceLeft testMatrix = !![4, 14; 8, 18] := by
    ext j j'
    fin_cases j <;> fin_cases j' <;>
      simp [partialTraceLeft, testMatrix, Fin.sum_univ_two] <;> norm_num
  rw [hA]
  norm_num [Matrix.trace, Fin.sum_univ_two]

end MathlibExtTest.LinearAlgebra.Matrix.PartialTraceTests
