/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TrinomialCoefficient
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

example : trinomialCoefficient 0 0 = 1 := by
  norm_num [trinomialCoefficient, Polynomial.coeff_one]

example : trinomialCoefficient 0 1 = 0 := by
  norm_num [trinomialCoefficient, Polynomial.coeff_one]

example : trinomialCoefficient 1 0 = 1 := by
  norm_num [trinomialCoefficient, Polynomial.coeff_add, Polynomial.coeff_one,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]

example : trinomialCoefficient 1 1 = 1 := by
  norm_num [trinomialCoefficient, Polynomial.coeff_add, Polynomial.coeff_one,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]

example : trinomialCoefficient 1 2 = 1 := by
  norm_num [trinomialCoefficient, Polynomial.coeff_add, Polynomial.coeff_one,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]

example : trinomialCoefficient 2 2 = 3 := by
  change ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℕ) ^ 2).coeff 2 = 3
  ring_nf
  norm_num [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
    Polynomial.coeff_X_pow]

example : trinomialCoefficient 2 5 = 0 := by
  change ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℕ) ^ 2).coeff 5 = 0
  ring_nf
  norm_num [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X,
    Polynomial.coeff_X_pow]

-- At columns zero and one, the negative-index terms must be omitted, not truncated to zero.
example : (0 : ℚ) / 2 * trinomialCoefficient 2 0 = 0 := by
  have h := trinomialCoefficient_absorption 2 0 (by decide)
  simp only [Nat.cast_zero, Nat.cast_ofNat] at h
  rw [h]
  norm_num

example : (1 : ℚ) / 2 * trinomialCoefficient 2 1 = 1 := by
  have h := trinomialCoefficient_absorption 2 1 (by decide)
  simp only [Nat.cast_one, Nat.cast_ofNat] at h
  rw [h]
  norm_num [trinomialCoefficient, Polynomial.coeff_add, Polynomial.coeff_one,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]

-- Both shifted terms contribute to the interior coefficient.
example : (2 : ℚ) / 2 * trinomialCoefficient 2 2 = 3 := by
  have h := trinomialCoefficient_absorption 2 2 (by decide)
  simp only [Nat.cast_ofNat] at h
  rw [h]
  norm_num [trinomialCoefficient, Polynomial.coeff_add, Polynomial.coeff_one,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]

example : (5 : ℚ) / 2 * trinomialCoefficient 2 5 = 0 := by
  have h := trinomialCoefficient_absorption 2 5 (by decide)
  simp only [Nat.cast_ofNat] at h
  rw [h]
  norm_num [trinomialCoefficient, Polynomial.coeff_add, Polynomial.coeff_one,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]

example : generalizedCentralTrinomial 3 5 0 = 1 :=
  generalizedCentralTrinomial_zero 3 5

example : generalizedCentralTrinomial 3 5 1 = 3 :=
  generalizedCentralTrinomial_one 3 5

example : generalizedCentralTrinomial 2 1 2 = 6 := by
  rw [generalizedCentralTrinomial_eq_sum]
  norm_num [Finset.sum_range_succ, Nat.choose]

example : generalizedCentralTrinomial (-3) (-2) 5 = 477 := by
  rw [generalizedCentralTrinomial_eq_sum]
  norm_num [Finset.sum_range_succ, Nat.choose]

#print axioms MetaMathlibExt.trinomialCoefficient
#print axioms MetaMathlibExt.generalizedCentralTrinomial_one
#print axioms MetaMathlibExt.generalizedCentralTrinomial_eq_sum

end MetaMathlibExt

end
