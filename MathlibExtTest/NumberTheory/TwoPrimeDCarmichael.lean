/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoPrimeDCarmichael
import Mathlib.Tactic.NormNum.LegendreSymbol

open MetaMathlibExt

-- Both allowed discriminant classes occur, including a negative discriminant.
example : IsDCarmichael (-4) (3 * 5) := by
  apply (isDCarmichael_mul_iff (by decide) (by decide) (by decide) (by decide)).2
  norm_num

example : IsDCarmichael 5 (17 * 19) := by
  apply (isDCarmichael_mul_iff (by decide) (by decide) (by decide) (by decide)).2
  norm_num

-- A twin pair with the signs in the opposite order.
example : ¬ IsDCarmichael 13 (3 * 5) := by
  rw [isDCarmichael_mul_iff (by decide) (by decide) (by decide) (by decide)]
  norm_num

-- The correct signs alone do not suffice when the prime gap exceeds two.
example : ¬ IsDCarmichael (-4) (3 * 13) := by
  rw [isDCarmichael_mul_iff (by decide) (by decide) (by decide) (by decide)]
  norm_num
