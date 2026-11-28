/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.RealZerosParityChangeBound
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.NormNum

open Polynomial MathlibExt.Algebra.RealZerosParityChangeBoundWanted

example : ¬ conjecture := conjecture_refuted

example : cTilde (C (7 : ℝ)) 0 = 49 := by
  norm_num [cTilde]

example : vVal (0 : Polynomial ℝ) = 0 := by
  have h : (Finset.range 1).filter (fun k => 0 < cTilde (0 : Polynomial ℝ) k) = ∅ := by
    ext
    simp [cTilde]
  unfold vVal posIndices
  rw [natDegree_zero, zero_add, h]
  simp

private noncomputable def quadratic : Polynomial ℝ := X ^ 2 + X + C 3

example : cTilde quadratic 1 = -1 := by
  norm_num [quadratic, cTilde, coeff_add, coeff_X_pow, coeff_X]

private theorem quadratic_posIndices : posIndices quadratic = [0, 2] := by
  have hdeg : quadratic.natDegree = 2 := by
    apply le_antisymm
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      have hk0 : k ≠ 0 := by omega
      have hk1 : k ≠ 1 := by omega
      have hk2 : k ≠ 2 := by omega
      simp [quadratic, coeff_X_pow, coeff_X, coeff_C_of_ne_zero hk0, hk2, Ne.symm hk1]
    · apply le_natDegree_of_ne_zero
      norm_num [quadratic, coeff_add, coeff_X_pow, coeff_X]
  have hr : Finset.range 3 = ({0, 1, 2} : Finset ℕ) := by decide
  have hf : ({0, 1, 2} : Finset ℕ).filter (fun k => 0 < cTilde quadratic k) = {0, 2} := by
    norm_num [Finset.filter_insert, Finset.filter_singleton, quadratic, cTilde, coeff_add,
      coeff_X_pow, coeff_X]
  have hs : ({0, 2} : Finset ℕ).sort (· ≤ ·) = [0, 2] := by
    rw [Finset.sort_insert, Finset.sort_singleton] <;> simp
  simpa [posIndices, hdeg, hr, hf] using hs

example : vVal quadratic = 0 := by
  unfold vVal
  rw [quadratic_posIndices]
  decide
