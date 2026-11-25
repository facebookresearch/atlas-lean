/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WilsonQuotients

open MathlibExt.NumberTheory.WilsonQuotientsWanted

-- The unit modulus allows the unique index zero.
example : (1 : ℤ) ≡ -1 [ZMOD 1] :=
  (neg_one_pow_mul_factorial_mul_factorial_modEq_neg_one_iff 1 0 (by decide) (by decide)).2
    (Or.inl rfl)

-- At the last index the complementary factorial is 0!.
example : (24 : ℤ) ≡ -1 [ZMOD 5] :=
  (neg_one_pow_mul_factorial_mul_factorial_modEq_neg_one_iff 5 4 (by decide) (by decide)).2
    (Or.inr (by decide))

-- An odd interior index gives a negative product.
example : (-36 : ℤ) ≡ -1 [ZMOD 7] :=
  (neg_one_pow_mul_factorial_mul_factorial_modEq_neg_one_iff 7 3 (by decide) (by decide)).2
    (Or.inr (by decide))

-- The composite modulus 4 rejects the product at its interior index 1.
example : ¬ ((-2 : ℤ) ≡ -1 [ZMOD 4]) :=
  (neg_one_pow_mul_factorial_mul_factorial_modEq_neg_one_iff 4 1 (by decide) (by decide)).not.mpr
    (by decide)
