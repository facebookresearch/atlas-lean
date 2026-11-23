/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.BernoulliFibonacciMultinomial

namespace MathlibExt.NumberTheory.FiniteSumsFibLucasWanted

open Finset

private noncomputable def weight (m n : ℕ) (j ℓ : Fin 2 → Fin (n + 1)) : ℝ :=
  Real.sqrt 5 ^ ((∑ i, (ℓ i).val) + m - n) *
    ((n.factorial : ℝ) / ((∏ i, ((j i).val.factorial : ℝ)) * ∏ i, ((ℓ i).val.factorial : ℝ))) *
    (m.choose n : ℝ) * (∏ i, (bernoulli (ℓ i).val : ℝ)) *
    ∏ i, ((Nat.fib ((j i).val + 1) : ℝ) / ((j i).val + 1 : ℕ))

-- At degree zero the only quadruple is zero.
example : weight 0 0 0 0 = 1 := by
  norm_num [weight]

-- Degree two is the first case in which the Bernoulli-index factorials affect the sum.
example :
    ∑ n ∈ range 3,
      ∑ p ∈ (univ : Finset ((Fin 2 → Fin (n + 1)) × (Fin 2 → Fin (n + 1)))).filter
          (fun p => (∑ i, (p.1 i).val) + (∑ i, (p.2 i).val) = n),
        weight 2 n p.1 p.2 = 1 :=
  sum_bernoulli_fib_two_eq_one 2

-- The term with Bernoulli indices (2, 0) contains a factor of 1/2!.
example : weight 2 2 0 ![2, 0] = 5 / 6 := by
  norm_num [weight, Fin.prod_univ_two, Fin.sum_univ_two, Nat.factorial, Real.sq_sqrt]

end MathlibExt.NumberTheory.FiniteSumsFibLucasWanted
