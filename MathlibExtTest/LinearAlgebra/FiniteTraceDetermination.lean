/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.LinearAlgebra.FiniteTraceDetermination
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Trace

open MathlibExt.LinearAlgebra.FiniteTraceDeterminationWanted

private def jordan (a b : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := !![a, b; 0, a]

private theorem jordan_mul (a b c d : ℚ) :
    jordan a b * jordan c d = jordan (a * c) (a * d + b * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jordan, Matrix.mul_apply, Fin.sum_univ_two]

private theorem jordan_pow (a b : ℚ) (n : ℕ) : ∃ c, jordan a b ^ n = jordan (a ^ n) c := by
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [jordan]
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    rw [pow_succ, hc, jordan_mul, pow_succ]
    exact ⟨_, rfl⟩

private theorem trace_jordan_pow (a b : ℚ) (n : ℕ) :
    LinearMap.trace ℚ (Fin 2 → ℚ) (Matrix.toLinAlgEquiv' (jordan a b) ^ n) = 2 * a ^ n := by
  obtain ⟨c, hc⟩ := jordan_pow a b n
  rw [← map_pow, hc]
  change LinearMap.trace ℚ (Fin 2 → ℚ) (jordan (a ^ n) c).toLin' = _
  rw [Matrix.trace_toLin'_eq]
  simp [Matrix.trace, Fin.sum_univ_two, jordan, two_mul]

private theorem isUnit_jordan (b : ℚ) : IsUnit (Matrix.toLinAlgEquiv' (jordan (-2) b)) := by
  change IsUnit (jordan (-2) b).toLin'
  apply Matrix.isUnit_toLin'_iff.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [jordan, Matrix.det_fin_two_of, isUnit_iff_ne_zero]
  norm_num

-- A scalar operator and a non-scalar Jordan block agree on power traces starting at the sixth.
example : (Matrix.toLinAlgEquiv' (jordan (-2) 0)).charpoly =
    (Matrix.toLinAlgEquiv' (jordan (-2) 1)).charpoly := by
  apply charpoly_eq_of_trace_powers _ _ 2 5
  · simp [Module.finrank_fintype_fun_eq_card]
  · simp [Module.finrank_fintype_fun_eq_card]
  · exact isUnit_jordan 0
  · exact isUnit_jordan 1
  · intro k _ _
    rw [trace_jordan_pow, trace_jordan_pow]

-- In dimension zero the trace interval is empty, even with a positive offset.
example : (1 : Module.End ℚ (Fin 0 → ℚ)).charpoly =
    (1 : Module.End ℚ (ULift (Fin 0 → ℚ))).charpoly := by
  apply charpoly_eq_of_trace_powers _ _ 0 7
  · simp [Module.finrank_fintype_fun_eq_card]
  · simp [Module.finrank_fintype_fun_eq_card, finrank_ulift]
  · exact isUnit_one
  · exact isUnit_one
  · intro k hk hkr
    omega
