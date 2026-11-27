/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.GFPFibSumChoose

namespace MetaMathlibExt

open Polynomial Finset

-- Setting d = 0 at an odd index isolates the last summand, including F₁ when k = 0.
example (g : ℤ[X]) (k : ℕ) :
    generalizedFibonacciPolynomial 0 1 0 g (2 * k + 1) = g ^ k := by
  rw [gfp_fib_eq_sum_choose (hn := by omega), Nat.add_sub_cancel, Nat.mul_div_cancel_left k
    (by decide : 0 < 2), sum_range_succ]
  have vanish (i : ℕ) (hi : i ∈ range k) : (0 : ℤ[X]) ^ (2 * k + 1 - 2 * i - 1) = 0 := by
    exact zero_pow (by have := mem_range.mp hi; omega)
  rw [sum_eq_zero fun i hi ↦ by rw [vanish i hi, mul_zero, zero_mul]]
  simp [show 2 * k + 1 - k - 1 = k by omega]

-- At an even index the last summand still contains a factor of d.
example (d g : ℤ[X]) :
    generalizedFibonacciPolynomial 0 1 d g 4 = d ^ 3 + 2 * d * g := by
  rw [gfp_fib_eq_sum_choose (hn := by decide)]
  change (∑ i ∈ range 2, ((4 - i - 1).choose i : ℤ[X]) * d ^ (4 - 2 * i - 1) * g ^ i) = _
  simp [sum_range_succ]

end MetaMathlibExt
