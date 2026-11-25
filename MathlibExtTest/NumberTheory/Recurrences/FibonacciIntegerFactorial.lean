/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.Recurrences.FibonacciIntegerFactorial

open MetaMathlibExt

-- At the first admissible index, the primitive prime 233 gives the negative sign.
example : 233 + 1 ≡ 0 [MOD 13] := by
  have hp : IntegerSequence.IsPrimitivePrimeDivisor (fun n => (Nat.fib n : ℤ)) 13 233 := by
    refine ⟨by norm_num, by decide, by decide, by decide, ?_⟩
    intro n hn hlt
    exact (show ∀ k < 13, 1 ≤ k → ¬ (233 : ℤ) ∣ Nat.fib k by decide) n hlt hn
  exact (primitive_prime_dvd_fib_modEq_one_or_neg_one (by decide) hp).resolve_left (by decide)

-- At the next index, 29 first divides F₁₄ and gives the positive sign.
example : 29 ≡ 1 [MOD 14] := by
  have hp : IntegerSequence.IsPrimitivePrimeDivisor (fun n => (Nat.fib n : ℤ)) 14 29 := by
    refine ⟨by norm_num, by decide, by decide, by decide, ?_⟩
    intro n hn hlt
    exact (show ∀ k < 14, 1 ≤ k → ¬ (29 : ℤ) ∣ Nat.fib k by decide) n hlt hn
  exact (primitive_prime_dvd_fib_modEq_one_or_neg_one (by decide) hp).resolve_right (by decide)
