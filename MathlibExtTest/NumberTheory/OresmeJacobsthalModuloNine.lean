/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OresmeJacobsthalModuloNine

/-! # Tests for the Jacobsthal congruence modulo nine -/

open MetaMathlibExt

-- The shift by one gives the first two scaled terms 1 and 2.
example : (2 : ℤ) ^ 0 * lucasU ⟨1, -2, by decide⟩ 1 ≡ 1 [ZMOD 9] :=
  two_pow_mul_jacobsthal_succ_modEq_nine 0

example : (2 : ℤ) ^ 1 * lucasU ⟨1, -2, by decide⟩ 2 ≡ 2 [ZMOD 9] :=
  two_pow_mul_jacobsthal_succ_modEq_nine 1

-- The first recurrence step gives 12, with residue 3.
example : (12 : ℤ) ≡ 3 [ZMOD 9] :=
  two_pow_mul_jacobsthal_succ_modEq_nine 2

-- At index eight the residue wraps to zero.
example : (2 : ℤ) ^ 8 * lucasU ⟨1, -2, by decide⟩ 9 ≡ 0 [ZMOD 9] :=
  (two_pow_mul_jacobsthal_succ_modEq_nine 8).trans (by decide)
