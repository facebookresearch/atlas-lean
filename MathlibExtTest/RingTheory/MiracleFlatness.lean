/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.MiracleFlatness

/-! # Tests for tensor injectivity along a principal ideal

Multiplication by a nonzero integer is injective on `ℤ`, so tensoring `2ℤ ⊆ ℤ` with `ℤ` is
injective.
-/

namespace MathlibExtTest.RingTheory.MiracleFlatness

open _root_.MathlibExt.RingTheory.MiracleFlatness

example : Function.Injective ((Ideal.span {(2 : ℤ)}).subtype.rTensor ℤ) :=
  rTensor_subtype_span_singleton_injective_of_isSMulRegular ℤ
    (IsSMulRegular.of_ne_zero (by norm_num : (2 : ℤ) ≠ 0))

end MathlibExtTest.RingTheory.MiracleFlatness
