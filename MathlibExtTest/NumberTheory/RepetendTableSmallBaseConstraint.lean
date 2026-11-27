/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RepetendTableSmallBaseConstraint

open MetaMathlibExt

-- The upper bound can be attained.
example : (2 : ℤ) ≠ (0 : ℤ) + 1 :=
  ne_add_one_of_sq_add_mul_mem 6 2 0 (by decide) (by decide)

-- The lower bound can be attained even when the base exceeds the modulus.
example : (10 : ℤ) ≠ (-14 : ℤ) + 1 :=
  ne_add_one_of_sq_add_mul_mem 7 10 (-14) (by decide) (by decide)
