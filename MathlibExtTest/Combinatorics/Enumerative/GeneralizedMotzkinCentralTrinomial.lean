/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GeneralizedMotzkinCentralTrinomial

/-! # Tests for generalized Motzkin numbers and central trinomial coefficients -/

open MetaMathlibExt LaurentPolynomial

-- With zero outer weight, the trinomial is constant, even at exponent zero.
example (b : ℤ) (n : ℕ) :
    centralTrinomial 0 b n = b ^ n ∧ generalizedMotzkin 0 b n = b ^ n := by
  simp only [centralTrinomial, generalizedMotzkin, trinomialLaurent, map_zero, zero_mul,
    zero_add, add_zero, ← map_pow, mul_sub, mul_one, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    T, AddMonoidAlgebra.coeff_mul_single_apply, C_apply]
  norm_num

-- At degree two, the Motzkin correction removes one of the two returning pairs of steps.
example (a b : ℤ) :
    centralTrinomial a b 2 = b ^ 2 + 2 * a ^ 2 ∧
      generalizedMotzkin a b 2 = b ^ 2 + a ^ 2 := by
  unfold centralTrinomial generalizedMotzkin trinomialLaurent
  rw [← single_eq_C_mul_T, ← single_eq_C_mul_T, ← single_eq_C]
  simp only [pow_two, mul_sub, mul_one, T, mul_add, add_mul, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_single,
    Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_apply]
  norm_num
  constructor <;> ring

-- At exponent zero, only the unshifted constant term contributes.
example : a005717 0 = 0 ∧ a005773 0 = 1 := by
  simp [a005717, a005773, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

-- The ordinary Motzkin numbers have unit weights.
example (n : ℕ) :
    2 * generalizedMotzkin 1 1 n = 3 * centralTrinomial 1 1 n +
      2 * centralTrinomial 1 1 (n + 1) - centralTrinomial 1 1 (n + 2) := by
  simpa using generalizedMotzkin_centralTrinomial_relation 1 1 n
