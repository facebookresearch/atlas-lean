/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FkPerfect
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.FkPerfectNotIsKLNearPerfectTwoTwoPowMul

/-! # No near `F`-perfect number of the form `2 ^ a * p`

This module proves that no number of the form $2^a p$ with $p$ prime is near $F$-perfect.
Near $F$-perfect numbers are defined in `MathlibExt.NumberTheory.FkPerfect`. For odd $p$ the
statement is the instance $\ell = 3$ of `not_isKLNearPerfect_two_two_pow_mul`, the paper's
Theorem 10, and the case $p = 2$ follows from `not_isNearFPerfect_two_pow_mul_prime_pow`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", *INTEGERS* 25 (2025), Article A86
(<https://math.colgate.edu/~integers/z86/z86.pdf>), Theorem 9.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **No near $F$-perfect number of the form $2^a p$.** For every prime $p$ and every natural
number $a$, the number $n = 2^a p$ is not near $F$-perfect: there is no divisor $d$ of $n$ with
$d < n$ and $\sigma_2(n) = n^2 + d^2 + 3n$, where $\sigma_2(n)$ is the sum of the squares of the
divisors of $n$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 9. -/
theorem not_isNearFPerfect_two_pow_mul_prime
    (p a : ℕ) (hp : p.Prime) :
    ¬ IsNearFPerfect (2 ^ a * p) := by
  rintro ⟨d, hdvd, hlt, hsum⟩
  by_cases h2 : p = 2
  · subst h2
    have h := not_isNearFPerfect_two_pow_mul_prime_pow 2 (a + 1) 0 Nat.prime_two ⟨0, rfl⟩
    have hn : (2 : ℕ) ^ (a + 1) * 2 ^ 0 = 2 ^ a * 2 := by ring
    rw [hn] at h
    exact h ⟨d, hdvd, hlt, hsum⟩
  · exact not_isKLNearPerfect_two_two_pow_mul 3 p a (by decide) hp (hp.odd_of_ne_two h2)
      ⟨d, hdvd, hlt, hsum⟩

end MathlibExt.NumberTheory.FkPerfectWanted
