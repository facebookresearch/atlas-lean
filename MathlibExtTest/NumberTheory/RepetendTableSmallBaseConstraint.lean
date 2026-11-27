/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RepetendTableSmallBaseConstraint

open MetaMathlibExt

-- A positive quotient with the residue at the lower bound.
example : (3 : ℤ) ≠ (1 : ℤ) + 1 :=
  ne_add_one_of_sq_add_mul_mem 7 3 (by decide) (by decide) (by decide)
    1 2 (by decide) (by decide) (by decide)

-- The upper bound can also be attained.
example : (8 : ℤ) ≠ (5 : ℤ) + 1 :=
  ne_add_one_of_sq_add_mul_mem 11 8 (by decide) (by decide) (by decide)
    5 9 (by decide) (by decide) (by decide)
