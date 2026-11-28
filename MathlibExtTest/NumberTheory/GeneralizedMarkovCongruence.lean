/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.GeneralizedMarkovCongruence

open MetaMathlibExt

-- For b = 0 the range of residues is empty, so the count is 0.
example (k : ℕ) : genMarkovCongruenceCount k 0 = 0 := by
  simp [genMarkovCongruenceCount]

-- Modulo 1 the only residue, x = 0, is a solution.
example : genMarkovCongruenceCount 3 1 = 1 := by decide

-- The bound is attained: x ^ 2 + 1 ≡ 0 (mod 5) has the two solutions x = 2 and x = 3.
example : genMarkovCongruenceCount 0 5 ≤ 2 :=
  genMarkovCongruenceCount_prime_le_two (by decide) 0

example : genMarkovCongruenceCount 0 5 = 2 := genMarkovCongruenceCount_zero_five

-- x ^ 2 + x + 1 ≡ 0 (mod 7) has the two solutions x = 2 and x = 4.
example : genMarkovCongruenceCount 1 7 = 2 := by decide

-- Modulo 2 there is one solution, x = 1, for even k, and none for odd k.
example : genMarkovCongruenceCount 0 2 = 1 := by decide

example : genMarkovCongruenceCount 1 2 = 0 := by decide

-- For k = 2 the quadratic is (x + 1) ^ 2, with the single double root x = p - 1.
example : genMarkovCongruenceCount 2 7 = 1 := by decide

-- The bound holds for every k, also for primes too large to enumerate.
example (k : ℕ) : genMarkovCongruenceCount k 1009 ≤ 2 :=
  genMarkovCongruenceCount_prime_le_two (by norm_num) k

-- Primality is needed: modulo 9 = 3 ^ 2 the congruence x ^ 2 + 7x + 1 ≡ 0 has the three
-- solutions x = 1, 4 and 7 (Gyoda and Maruyama, Remark 4.19).
example : genMarkovCongruenceCount 7 9 = 3 := by decide

example : ¬ genMarkovCongruenceCount 7 9 ≤ 2 := by decide

-- The bound is attained modulo 5 ^ 2, with roots 7 and 18.
example : ((Finset.range (5 ^ 2)).filter fun x => 5 ^ 2 ∣ x ^ 2 + 1) = {7, 18} := by decide

example : genMarkovCongruenceCount 0 (5 ^ 2) = 2 := by decide

example : genMarkovCongruenceCount 0 (5 ^ 2) ≤ 2 :=
  genMarkovCongruenceCount_prime_pow_le_two (p := 5) (m := 2) (k := 0)
    (hp := by decide) (hp2 := by decide) (hm := by decide) (hk := by decide)

-- The discriminant is also nonzero modulo 3, but there are no roots modulo 3 ^ 2.
example : genMarkovCongruenceCount 0 (3 ^ 2) = 0 := by decide

example : genMarkovCongruenceCount 0 (3 ^ 2) ≤ 2 :=
  genMarkovCongruenceCount_prime_pow_le_two (p := 3) (m := 2) (k := 0)
    (hp := by decide) (hp2 := by decide) (hm := by decide) (hk := by decide)
