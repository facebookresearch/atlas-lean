/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoComplexityComplexityLPowAddPow

/-! # Tests for the complexity of a sum of two powers -/

set_option autoImplicit false

namespace MathlibExtTest.NumberTheory.TwoComplexityComplexityLPowAddPow

open MathlibExt.NumberTheory.TwoComplexityWanted

example : complexityL 3 54 = 4 :=
  complexityL_pow_add_pow 3 3 3 (by decide) (by decide) (by decide)

example : complexityL 3 90 = 5 :=
  complexityL_pow_add_pow 3 4 2 (by decide) (by decide) (by decide)

example : complexityL 2 40 = 6 :=
  complexityL_pow_add_pow 2 5 3 (by decide) (by decide) (by decide)

example : complexityL 2 4 = 2 ∧ complexityL 2 6 = 3 :=
  complexityL_two_pow_and_add 2 1 (by decide) (by decide)

end MathlibExtTest.NumberTheory.TwoComplexityComplexityLPowAddPow
