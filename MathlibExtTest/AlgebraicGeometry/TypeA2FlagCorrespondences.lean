/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.TypeA2FlagCorrespondences

noncomputable section

open MathlibExt.LinearAlgebra.HermitianFlags
open MathlibExt.AlgebraicGeometry.TypeA2FlagCorrespondences

private def secondMatrices : Fin 4 → Mat 3 :=
  ![0, Matrix.diagonal ![0, 1, 0], Matrix.diagonal ![1, 1, 0], 1]

private def secondFlag : Flag 3 := ⟨secondMatrices, {
  zero := rfl
  top := rfl
  hermitian := by
    intro i
    ext j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [secondMatrices]
  idempotent := by
    intro i
    ext j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [secondMatrices, Matrix.mul_apply, Fin.sum_univ_three]
  trace := by
    intro i
    fin_cases i <;> norm_num [secondMatrices, Matrix.trace, Fin.sum_univ_three]
  nested := by
    intro i j
    ext k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [secondMatrices, Matrix.mul_apply, Fin.sum_univ_three]
}⟩

/-- Changing the coordinate line inside its plane is a first-root step. -/
example : Adjacent 0 standardFlag secondFlag := by
  intro j hj
  fin_cases j <;> simp_all [simpleIndex, standardFlag, standardMatrices,
    secondFlag, secondMatrices]

/-- The same pair is excluded from the plane-changing correspondence. -/
example : ¬ Adjacent 1 standardFlag secondFlag := by
  intro h
  have h1 := h 1 (by decide)
  have hentry := congrArg (fun A : Mat 3 => A 0 0) h1
  norm_num [standardFlag, standardMatrices, secondFlag, secondMatrices] at hentry
