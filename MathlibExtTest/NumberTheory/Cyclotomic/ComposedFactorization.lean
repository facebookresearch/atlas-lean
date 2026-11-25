/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Cyclotomic.ComposedFactorization

open MetaMathlibExt Polynomial

-- With prime 2 repeated and exponents 1, 0, 2, the middle block contributes no factor.
example : (X ^ 8 - 1 : ℤ[X]) = (X - 1) * ((X + 1) * ((X ^ 2 + 1) * (X ^ 4 + 1))) := by
  have h := X_pow_sub_one_eq_mul_prod_cyclotomic_comp 3 (fun _ => 2)
    (fun i => if i = 1 then 1 else if i = 2 then 0 else 2) (fun _ _ => Nat.prime_two)
  simpa [Finset.prod_Icc_succ_top, Finset.prod_Ico_succ_top, cyclotomic_two,
    add_comp, mul_assoc] using h
