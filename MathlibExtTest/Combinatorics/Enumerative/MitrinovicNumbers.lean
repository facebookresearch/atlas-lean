/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.MitrinovicNumbers
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for the binomial expansion of Mitrinović's numbers -/

open MetaMathlibExt

-- All three terms contribute to the linear coefficient in row three.
example (a b : ℂ) : mitrinovicR a b 3 1 = 3 * a ^ 2 + 6 * a * b + 2 * b ^ 2 := by
  rw [mitrinovicR_eq_sum_mitrinovicR_zero]
  norm_num [Finset.sum_range_succ, Nat.choose, mitrinovicR]
  ring

-- At zero step size the row polynomial is a power of a single linear factor.
example (a : ℂ) : mitrinovicR a 0 4 3 = -4 * a := by
  rw [mitrinovicR_eq_sum_mitrinovicR_zero]
  norm_num [Finset.sum_range_succ, Nat.choose, mitrinovicR]

-- Above the diagonal the truncated sum has one term and that term vanishes.
example (a b : ℂ) : mitrinovicR a b 2 4 = 0 := by
  rw [mitrinovicR_eq_sum_mitrinovicR_zero]
  norm_num [Finset.sum_range_succ, mitrinovicR]
