/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModifiedDegenerateBernoulliThreeTerm

namespace MetaMathlibExt.modifiedDegenerateBernoulli_three_term

local notation "B" => modifiedDegenerateBernoulli

-- At the first allowed degree, both endpoints of each sum contribute.
example (lam x y z : ℂ) (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) (hxyz : x + y + z = 1) :
    (B lam 1 x * B lam 0 y - B lam 0 x * B lam 1 y) +
      (B lam 1 y * B lam 0 z - B lam 0 y * B lam 1 z) +
      (B lam 1 z * B lam 0 x - B lam 0 z * B lam 1 x) = 0 := by
  have h := modifiedDegenerateBernoulli_three_term 1 (by decide) lam hlam hlam1
    (1 / 3) (1 / 3) (1 / 3) x y z (by norm_num) hxyz
  norm_num [Finset.sum_range_succ, Ring.choose_zero_right, Ring.choose_one_right] at h
  linear_combination (9 : ℂ) * h

private theorem choose_two (a : ℂ) : Ring.choose a 2 = a * (a - 1) / 2 := by
  rw [Ring.choose_eq_smul, descPochhammer_succ_right, descPochhammer_one,
    Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X]
  norm_num [smul_eq_mul]
  ring

-- Weights -1, 3/2, 3/2 give nonzero binomial coefficients at degree two.
example (lam x y z : ℂ) (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) (hxyz : x + y + z = 1) :
    B lam 0 0 * (B lam 2 x + B lam 2 y + B lam 2 z) +
      2 * (B lam 1 x * B lam 1 y + B lam 1 y * B lam 1 z + B lam 1 z * B lam 1 x) = 0 := by
  have h := modifiedDegenerateBernoulli_three_term 2 (by decide) lam hlam hlam1
    (-1) (3 / 2) (3 / 2) x y z (by norm_num) hxyz
  have hz (u : ℂ) : B lam 0 u = B lam 0 0 := by simp [modifiedDegenerateBernoulli]
  norm_num [Finset.sum_range_succ, Ring.choose_zero_right, Ring.choose_one_right, choose_two] at h
  simp only [hz] at h
  linear_combination (8 / 9 : ℂ) * h

end MetaMathlibExt.modifiedDegenerateBernoulli_three_term
