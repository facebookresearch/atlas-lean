/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MonotoneColumnPermanent
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Notation

open MathlibExt.Combinatorics.MonotoneColumnPermanentAMR156Problem0025Wanted
open Polynomial

example (A : Matrix (Fin 0) (Fin 0) ℝ) : permanentAddXJ A = 1 :=
  Matrix.permanent_isEmpty

-- When every column is constant, all permutation products agree.
example {n : ℕ} (a : Fin n → ℝ) :
    permanentAddXJ (Matrix.of fun _ j => a j) = n.factorial * ∏ j, (C (a j) + X) := by
  simp [permanentAddXJ, Matrix.permanent, Fintype.card_perm, nsmul_eq_mul]

-- The two permutation products are (X - 2)(X + 3) and X(X + 1).
private def mixed : Matrix (Fin 2) (Fin 2) ℝ := !![-2, 1; 0, 3]

example : permanentAddXJ mixed = 2 * X ^ 2 + 2 * X - 6 := by
  rw [permanentAddXJ, Matrix.permanent, ← Equiv.Perm.decomposeFin.symm.sum_comp,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [Finset.univ_unique, Fin.prod_univ_succ, mixed, Equiv.swap_apply_def]
  rw [show C (2 : ℝ) = 2 from map_ofNat _ _, show C (3 : ℝ) = 3 from map_ofNat _ _]
  ring

example : ((permanentAddXJ mixed).map (algebraMap ℝ ℂ)).IsRealRooted := by
  apply monotoneColumnPermanentConjecture_holds
  intro i k j h
  fin_cases i <;> fin_cases k <;> fin_cases j <;> norm_num [mixed] at *
