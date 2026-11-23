/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.TraceNormDuality
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup

namespace PhyslibExt.QuantumInfo.TraceNormDualityTests

open PhyslibExt.QuantumInfo.TraceNormDuality

/-- Diagonal value over `Fin 3`, through the diagonal computation. -/
theorem diagonal_Fin3_value :
    (Matrix.diagonal ![1, -2, Complex.I]).traceNorm = 4 := by
  rw [traceNorm_diagonal, Fin.sum_univ_three]
  simp [Complex.norm_I]
  norm_num

/-- Attainment is nonvacuous over `Fin 2`, from attainment and diagonal. -/
theorem attainment_nonvacuous_Fin2 :
    ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
      ‖((U : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose *
        Matrix.diagonal ![3, -4]).trace‖ = 7 := by
  obtain ⟨U, hU⟩ :=
    exists_unitary_norm_tr_eq_traceNorm (Matrix.diagonal ![3, -4])
  refine ⟨U, hU.trans ?_⟩
  rw [traceNorm_diagonal, Fin.sum_univ_two]
  simp
  norm_num

#print axioms diagonal_Fin3_value
#print axioms attainment_nonvacuous_Fin2
#print axioms traceNorm_eq_max_norm_tr_U
#print axioms exists_unitary_norm_tr_eq_traceNorm
#print axioms norm_tr_unitary_conjTranspose_mul_le_traceNorm
#print axioms traceNorm_diagonal
#print axioms Matrix.traceNorm_eq_max_re_tr_U

end PhyslibExt.QuantumInfo.TraceNormDualityTests
