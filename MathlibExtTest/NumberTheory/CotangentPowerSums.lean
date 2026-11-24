/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.CotangentPowerSums

open MetaMathlibExt

-- Opposite parities, once with the lowest positive column and once with an even column.
example : cotangentPowerCoeff 2 1 = 0 :=
  cotangentPowerCoeff_eq_zero_of_mod_two_ne (by decide) (by decide) (by decide)

example : cotangentPowerCoeff 5 2 = 0 :=
  cotangentPowerCoeff_eq_zero_of_mod_two_ne (by decide) (by decide) (by decide)

-- A same-parity coefficient off the diagonal is nonzero.
example : cotangentPowerCoeff 4 2 = -4 / 3 := by
  norm_num [cotangentPowerCoeff, Finset.sum_Icc_succ_top, Nat.stirlingFirst, Nat.choose,
    Nat.factorial]

-- Column zero shows why the parity theorem assumes a positive column index.
example : cotangentPowerCoeff 1 0 = 1 := by
  norm_num [cotangentPowerCoeff, Finset.sum_Icc_succ_top, Nat.stirlingFirst]
