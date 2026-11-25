/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlzerRichardsSabarIdentity
import Mathlib.Tactic.LinearCombination

open Finset MetaMathlibExt

-- At the least allowed exponent, the one-term sum vanishes for every complex argument.
example (z : ℂ) :
    ∑ k ∈ range 1, (-1 : ℂ) ^ (1 - k - 1) * k * Ring.choose z k *
      Ring.choose (z - k - 1) (1 - k - 1) = 0 := by
  simpa only [pow_one, descPochhammer_one, Polynomial.eval_X, sub_self] using
    (pow_sub_descPochhammer_eq_sum_choose (p := 1) (by decide) z).symm

-- At the imaginary unit, the cubic case has nonzero real and imaginary parts.
example :
    ∑ k ∈ range 3, (-1 : ℂ) ^ (3 - k - 1) * (k : ℂ) ^ 3 * Ring.choose Complex.I k *
      Ring.choose (Complex.I - k - 1) (3 - k - 1) = -3 - 2 * Complex.I := by
  rw [← pow_sub_descPochhammer_eq_sum_choose (p := 3) (by decide)]
  simp only [descPochhammer_succ_eval, descPochhammer_zero, Polynomial.eval_one, Nat.cast_zero,
    sub_zero, one_mul, Nat.cast_one, Nat.cast_ofNat]
  linear_combination 3 * Complex.I_sq
