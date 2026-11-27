/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OresmeLucasModuloFive

/-! # Tests for the weighted Lucas congruence modulo five -/

open MetaMathlibExt

example : 2 ^ 0 * lucasNumber 1 ≡ 1 [MOD 5] :=
  two_pow_mul_lucasNumber_succ_modEq_five 0

example : 2 ^ 1 * lucasNumber 2 ≡ 1 [MOD 5] :=
  two_pow_mul_lucasNumber_succ_modEq_five 1

example : 2 ^ 5 * lucasNumber 6 ≡ 1 [MOD 5] :=
  two_pow_mul_lucasNumber_succ_modEq_five 5
