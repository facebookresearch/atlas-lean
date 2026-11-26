/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Diophantine.BisectorEquationIntZero

/-! # Tests for `MathlibExt.NumberTheory.Diophantine.BisectorEquationIntZero` -/

namespace MathlibExtTest.BisectorEquationIntZero

open MetaMathlibExt

-- With `a = 0`, every integer solution of the bisector equation has `b = 0`.
example (b c : ℤ) (h : (0 - c) ^ 2 * (b ^ 2 + 1) = (b - c) ^ 2 * (0 ^ 2 + 1)) : b = 0 := by
  simpa using (bisector_equation_int_zero 0 b c (Or.inl rfl) h).symm

-- With `b = 0`, the slope `a = 2` has no integer bisector slope `c`.
example (c : ℤ) : (2 - c) ^ 2 * (0 ^ 2 + 1) ≠ (0 - c) ^ 2 * (2 ^ 2 + 1) := by
  intro h
  have := bisector_equation_int_zero 2 0 c (Or.inr rfl) h
  norm_num at this

-- The trivial solution `a = b = c = 0` is allowed.
example : |(0 : ℤ)| = |(0 : ℤ)| :=
  bisector_equation_int_zero 0 0 0 (Or.inl rfl) (by norm_num)

#print axioms bisector_equation_int_zero

end MathlibExtTest.BisectorEquationIntZero
