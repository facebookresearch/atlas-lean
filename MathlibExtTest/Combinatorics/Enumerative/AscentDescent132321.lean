/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AscentDescent132321
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

open MetaMathlibExt PowerSeries

namespace AscentDescent132321Test

private abbrev R := MvPolynomial (Fin 2) ℚ
private noncomputable abbrev p : R := MvPolynomial.X 0
private noncomputable abbrev q : R := MvPolynomial.X 1
private noncomputable abbrev G := ascDesGF (pattern3 ![0, 2, 1]) (pattern3 ![2, 1, 0])

private theorem cleared :
    G - X * (C (3 * p) * G) + X ^ 2 * (C (3 * p ^ 2) * G) -
      X ^ 3 * (C (p ^ 3) * G) =
    1 + X * C (1 - 3 * p) + X ^ 2 * C (-2 * p + 3 * p ^ 2 + q) +
      X ^ 3 * C (p ^ 2 - p ^ 3) := by
  have h := ascDesGF_132_321
  dsimp only at h
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, map_neg]
  linear_combination h

-- The empty permutation contributes one to the constant coefficient.
private theorem constant : coeff 0 G = 1 := by
  simpa [coeff_one, coeff_X_pow_mul'] using congrArg (coeff 0) cleared

-- At length four there is one increasing permutation and six avoiders with one descent.
example : coeff 4 G = p ^ 3 + 6 * p ^ 2 * q := by
  have h₁ := congrArg (coeff 1) cleared
  have h₂ := congrArg (coeff 2) cleared
  have h₃ := congrArg (coeff 3) cleared
  have h₄ := congrArg (coeff 4) cleared
  norm_num only [map_add, map_sub, coeff_one, coeff_X_pow_mul', coeff_succ_X_mul,
    coeff_C_mul, coeff_C, ite_true, ite_false, constant] at h₁ h₂ h₃ h₄
  have c₁ : coeff 1 G = 1 := by linear_combination h₁
  rw [c₁] at h₂ h₃ h₄
  have c₂ : coeff 2 G = p + q := by linear_combination h₂
  rw [c₂] at h₃ h₄
  have c₃ : coeff 3 G = p ^ 2 + 3 * p * q := by linear_combination h₃
  rw [c₃] at h₄
  linear_combination h₄

end AscentDescent132321Test
