/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Polynomial.PerronIrreducibility
import Mathlib.Tactic.NormNum

/-!
# Examples for Perron's irreducibility criterion
-/

open MetaMathlibExt Polynomial

-- At degree one the sum over the lower coefficients is empty.
example : Irreducible (X + C (2 : ℤ)) := by
  apply perron_irreducible (monic_X_add_C 2)
  · rw [natDegree_X_add_C]
  · rw [coeff_add, coeff_X_zero, coeff_C_zero, zero_add]
    decide
  · rw [natDegree_X_add_C, Nat.sub_self, Finset.sum_range_zero, add_zero,
      coeff_add, coeff_X_zero, coeff_C_zero, zero_add]
    decide

-- The dominant coefficient is negative and the strict inequality has the smallest integral gap.
example : Irreducible (X ^ 3 + (C (-5 : ℤ) * X ^ 2 + (X + C 2))) := by
  have htail : (C (-5 : ℤ) * X ^ 2 + (X + C 2)).degree < ((3 : ℕ) : WithBot ℕ) := by
    apply lt_of_le_of_lt (degree_add_le _ _)
    rw [max_lt_iff, degree_X_add_C]
    exact ⟨(degree_C_mul_X_pow_le 2 (-5 : ℤ)).trans_lt (by decide), by decide⟩
  have hdeg : (X ^ 3 + (C (-5 : ℤ) * X ^ 2 + (X + C 2))).natDegree = 3 := by
    rw [natDegree_add_eq_left_of_degree_lt (by simpa only [degree_X_pow] using htail),
      natDegree_X_pow]
  apply perron_irreducible (monic_X_pow_add htail)
  · rw [hdeg]
    decide
  · norm_num [coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X]
  · rw [hdeg]
    norm_num [Finset.sum_range_succ, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X]
