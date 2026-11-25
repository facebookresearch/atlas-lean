/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.GeneralizedEigenvalueInterlacing
import Mathlib.Tactic.FinCases

open Matrix Polynomial
open scoped ComplexOrder

-- The pencil has roots t and −t, and the principal pencil has root zero.
-- This includes a repeated root at t = 0 and strict interlacing at every t > 0.
example (t : ℝ) (ht : 0 ≤ t) : -t ≤ 0 ∧ 0 ≤ t := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![0, 2 * (t : ℂ); 2 * (t : ℂ), 0]
  let B : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, 4]
  have hA : A.IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, Matrix.conjTranspose_apply]
  have hB : B.PosDef := PosDef.diagonal (by intro i; fin_cases i <;> norm_num)
  have hdet : (A.map C - (X : ℂ[X]) • B.map C).det =
      C 4 * ((X - C (t : ℂ)) * (X - C (-t : ℂ))) := by
    simp [det_fin_two, A, B, map_ofNat]
    ring
  apply MetaMathlibExt.generalizedEigenvalue_interlacing 1 (by decide) A B hA hB
    ![t, -t] ?_ ?_ (fun _ => 0) antitone_const ?_ 0
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · rw [hdet, roots_C_mul _ (by norm_num),
      roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
      roots_X_sub_C, roots_X_sub_C, Fin.univ_val_map]
    simp [List.ofFn_succ]
    rfl
  · simp [A, B]
