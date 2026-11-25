/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AscentDescent123132
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

open MetaMathlibExt PowerSeries
open MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

namespace AscentDescent123132Test

private abbrev R := MvPolynomial (Fin 2) ℚ
private noncomputable abbrev p : R := MvPolynomial.X 0
private noncomputable abbrev q : R := MvPolynomial.X 1
private noncomputable abbrev G := ascDesGF (pattern3 ![0, 1, 2]) (pattern3 ![0, 2, 1])

private theorem cleared :
    G - X * (C (2 * q) * G) + X ^ 2 * (C (q ^ 2 - p * q) * G) =
      1 + X * C (1 - 2 * q) + X ^ 2 * C (p - q - p * q + q ^ 2) := by
  have h := ascDesGF_123_132
  dsimp only at h
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
  linear_combination h

-- Empty and singleton permutations contribute one; at length two both orders are allowed.
private theorem c0 : coeff 0 G = 1 := by
  simpa [coeff_one, coeff_X_pow_mul'] using congrArg (coeff 0) cleared

private theorem c1 : coeff 1 G = 1 := by
  have h := congrArg (coeff 1) cleared
  norm_num only [map_add, map_sub, sub_mul, coeff_one, coeff_X_pow_mul', coeff_succ_X_mul,
    coeff_C_mul, coeff_C, ite_true, ite_false, c0] at h
  linear_combination h

private theorem c2 : coeff 2 G = p + q := by
  have h := congrArg (coeff 2) cleared
  norm_num only [map_add, map_sub, sub_mul, coeff_one, coeff_X_pow_mul', coeff_succ_X_mul,
    coeff_C_mul, coeff_C, ite_true, ite_false, c0, c1] at h
  linear_combination h

private theorem c3 : coeff 3 G = 3 * p * q + q ^ 2 := by
  have h := congrArg (coeff 3) cleared
  norm_num only [map_add, map_sub, sub_mul, coeff_one, coeff_X_pow_mul', coeff_succ_X_mul,
    coeff_C_mul, coeff_C, ite_true, ite_false, c1, c2] at h
  linear_combination h

example : coeff 4 G = p ^ 2 * q + 6 * p * q ^ 2 + q ^ 3 := by
  have h := congrArg (coeff 4) cleared
  norm_num only [map_add, map_sub, sub_mul, coeff_one, coeff_X_pow_mul', coeff_succ_X_mul,
    coeff_C_mul, coeff_C, ite_true, ite_false, c2, c3] at h
  linear_combination h

private def endingCount (n : ℕ) (up : Bool) (ascents : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin (n + 2)) =>
    ¬ HasPattern σ (pattern3 ![0, 1, 2]) ∧ ¬ HasPattern σ (pattern3 ![0, 2, 1]) ∧
      decide (σ (Fin.last n).castSucc < σ (Fin.last (n + 1))) = up ∧
      permAscents σ = ascents).card

-- Of the three avoiders of length three with one ascent, two end with that ascent.
-- At length four the only avoider with two ascents ends in an ascent, not a descent.
example : endingCount 1 true 1 = 2 ∧ endingCount 1 false 1 = 1 ∧
    endingCount 2 true 2 = 1 ∧ endingCount 2 false 2 = 0 := by
  decide +kernel

end AscentDescent123132Test
