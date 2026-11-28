/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Ring.GeomSum

/-!
# Sum of divisors of powers of two

For every natural number $k$, the positive divisors of $2^k$ sum to $2^{k+1}-1$.
The proof evaluates the geometric sum given by Mathlib's prime-power divisor-sum formula.
-/

namespace MetaMathlibExt

/-- **Sum of divisors of a power of two.** For every natural number $k$, if $\sigma(n)$ denotes
the sum of the positive divisors of $n$, then $\sigma(2^k) + 1 = 2^{k+1}$. -/
public theorem sigma_two_pow_add_one (k : ℕ) :
    ArithmeticFunction.sigma 1 (2 ^ k) + 1 = 2 ^ (k + 1) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  simpa only [one_add_one_eq_two, mul_one] using geom_sum_mul_add (1 : ℕ) (k + 1)

end MetaMathlibExt
