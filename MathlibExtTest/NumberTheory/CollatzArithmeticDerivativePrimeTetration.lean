/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CollatzArithmeticDerivativePrimeTetration

namespace MetaMathlibExt

-- The even branch takes 2^2 to the prime 2, whose derivative is 1.
example : ¬ ∃ q : ℕ, q.Prime ∧ collatzAccelerated (2 ^ 2) = q ^ q := by
  have hp : Nat.Prime 2 := by decide
  apply (not_congr (arithmeticDerivative_collatz_comm_prime_tetration_iff 2 hp)).mp
  have hD : arithmeticDerivative (2 ^ 2) = 2 ^ 2 := by
    rw [pow_two, arithmeticDerivative_mul, arithmeticDerivative_prime hp]
    decide
  have hC : collatzAccelerated (2 ^ 2) = 2 := by decide
  rw [hD, hC, arithmeticDerivative_prime hp]
  decide

-- The odd branch takes 3^3 to the prime 41, whose derivative is again 1.
example : ¬ ∃ q : ℕ, q.Prime ∧ collatzAccelerated (3 ^ 3) = q ^ q := by
  have hp : Nat.Prime 3 := by decide
  have hq : Nat.Prime 41 := by decide
  apply (not_congr (arithmeticDerivative_collatz_comm_prime_tetration_iff 3 hp)).mp
  have hD : arithmeticDerivative (3 ^ 3) = 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 3 * (3 * 3) by decide]
    simp only [arithmeticDerivative_mul, arithmeticDerivative_prime hp]
  have hC : collatzAccelerated (3 ^ 3) = 41 := by decide
  rw [hD, hC, arithmeticDerivative_prime hq]
  decide

end MetaMathlibExt
