/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum
import MathlibExt.LinearAlgebra.Matrix.InverseEigenvalues

-- The reciprocal eigenvalue of the inverse of the one-by-one matrix `[2]` is `1/2`.
example : Module.End.HasEigenvector
    (Matrix.toLin' ((2 : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ))⁻¹) (2 : ℚ)⁻¹
    (fun _ => 1) := by
  let M : Matrix (Fin 1) (Fin 1) ℚ := (2 : ℚ) • 1
  have hM : IsUnit M.det := by simp [M]
  have hx : Module.End.HasEigenvector (Matrix.toLin' M) (2 : ℚ) (fun _ => 1) := by
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    constructor
    · simp [M]
    · intro h
      have h0 := congrFun h (0 : Fin 1)
      norm_num at h0
  exact (M.hasEigenvector_toLin'_inv_iff hM (by norm_num) _).mp hx
