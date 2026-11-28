/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AscentDescent213231
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

open PowerSeries MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

private abbrev R := MvPolynomial (Fin 2) ℚ
private noncomputable abbrev p : R := MvPolynomial.X 0
private noncomputable abbrev q : R := MvPolynomial.X 1
private noncomputable abbrev g := ascDesGF (pattern3 ![1, 0, 2]) (pattern3 ![1, 2, 0])

private theorem series_identity : g - C p * (X * g) - C q * (X * g) =
    1 + X - C p * X - C q * X := by
  have h : (1 - C p * X - C q * X) * g = 1 + X - C p * X - C q * X := ascDesGF_213_231
  rwa [sub_mul, sub_mul, one_mul, mul_assoc, mul_assoc] at h

-- The empty and singleton permutations have weight one.
private theorem coeff_zero_g : coeff 0 g = 1 := by
  simpa using congrArg (coeff (R := R) 0) series_identity

private theorem coeff_one_g : coeff 1 g = 1 := by
  have hzero : constantCoeff g = 1 := (coeff_zero_eq_constantCoeff_apply g).symm ▸ coeff_zero_g
  have hc := congrArg (coeff (R := R) 1) series_identity
  simp [coeff_C_mul, hzero] at hc
  linear_combination hc

private theorem coeff_step (n : ℕ) : coeff (n + 2) g = (p + q) * coeff (n + 1) g := by
  have he := congrArg (coeff (R := R) (n + 2)) series_identity
  simp [coeff_C_mul, coeff_X] at he
  linear_combination he

-- At length two the increasing and decreasing permutations contribute p and q.
example : coeff 2 g = p + q := by
  rw [coeff_step 0, coeff_one_g, mul_one]

-- At length three both mixed weights occur, while 213 and 231 themselves do not.
example : coeff 3 g = p ^ 2 + 2 * p * q + q ^ 2 := by
  rw [coeff_step 1, coeff_step 0, coeff_one_g]
  ring

end MetaMathlibExt
