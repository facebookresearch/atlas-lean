/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.SmallProductRemainder

open MetaMathlibExt

-- The product is below the modulus even though the right factor is not.
example : (0 * 100) % 7 = 0 * (100 % 7) :=
  mul_mod_eq_mul_mod_of_mul_lt 0 100 7 (by decide)

-- Both factors are positive and the product is just below the modulus.
example : (3 * 4) % 13 = 3 * (4 % 13) :=
  mul_mod_eq_mul_mod_of_mul_lt 3 4 13 (by decide)
