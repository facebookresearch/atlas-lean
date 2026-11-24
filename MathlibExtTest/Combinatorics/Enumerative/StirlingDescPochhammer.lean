/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.StirlingDescPochhammer
import Mathlib.Tactic.Ring

open MetaMathlibExt Polynomial

example : descPochhammer ℤ 0 = 1 := by
  rw [descPochhammer_eq_sum_signedStirlingFirst]
  simp

example : descPochhammer ℤ 3 = X ^ 3 - 3 * X ^ 2 + 2 * X := by
  rw [descPochhammer_eq_sum_signedStirlingFirst]
  simp [Finset.sum_range_succ, signedStirlingFirst, Nat.stirlingFirst]
  ring
