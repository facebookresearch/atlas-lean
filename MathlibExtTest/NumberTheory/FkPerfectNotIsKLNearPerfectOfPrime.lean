/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfectNotIsKLNearPerfectOfPrime
/-! # Tests for primes and near-perfect numbers

These tests apply the prime exclusion theorem at zero and positive exponents,
and check that primes satisfy near-perfectness when `ℓ = 0`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia,
"On Near `F_k`-Perfect and Deficient `F_k`-Perfect Numbers", *INTEGERS* 25 (2025),
Article A86 (<https://math.colgate.edu/~integers/z86/z86.pdf>), Proposition 2.
-/

namespace MathlibExtTest.NumberTheory.FkPerfect

open MathlibExt.NumberTheory.FkPerfectWanted

example : ¬ IsKLNearPerfect 0 1 2 :=
  not_isKLNearPerfect_of_prime 0 1 2 (by decide) (by decide)

example : ¬ IsKLNearPerfect 2 3 5 :=
  not_isKLNearPerfect_of_prime 2 3 5 (by decide) (by decide)

example (k p : ℕ) (hp : p.Prime) : IsKLNearPerfect k 0 p := by
  refine ⟨1, one_dvd p, hp.one_lt, ?_⟩
  simp only [hp.sum_divisors, one_pow, zero_mul, add_zero]

end MathlibExtTest.NumberTheory.FkPerfect
