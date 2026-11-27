/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import MathlibExt.NumberTheory.FkPerfect
public import MathlibExt.NumberTheory.NearPerfectTwoPrimePower
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! # No near `F`-perfect number of the form `2 * p ^ a`

For an odd prime `p`, the divisibility `p ^ 2 ∣ 1 + 2 ^ 2` supplied by
`klNearPerfectWith_two_mul_prime_pow_imp` is impossible since `p ^ 2 ≥ 9 > 5`.
For `p = 2`, the number `2 * 2 ^ a = 2 ^ (a + 1) * 2 ^ 0` is excluded by
`not_isNearFPerfect_two_pow_mul_prime_pow` with the even exponent `0`. The main result is
`not_isNearFPerfect_two_mul_prime_pow`.
Near `F`-perfect numbers are defined in `MathlibExt.NumberTheory.FkPerfect`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", *INTEGERS* 25 (2025), Article A86
(<https://math.colgate.edu/~integers/z86/z86.pdf>), Theorem 13.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **No near $F$-perfect number of the form $2p^a$.** For every prime $p$ and every natural
number $a$, the number $n = 2p^a$ is not near $F$-perfect: there is no divisor $d$ of $n$ with
$d < n$ and $\sigma_2(n) = n^2 + d^2 + 3n$, where $\sigma_2(n)$ is the sum of the squares of the
divisors of $n$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 13. -/
theorem not_isNearFPerfect_two_mul_prime_pow
    (p a : ℕ) (hp : p.Prime) :
    ¬ IsNearFPerfect (2 * p ^ a) := by
  rintro ⟨d, hdvd, hlt, hsum⟩
  by_cases h2 : p = 2
  · subst h2
    have h := not_isNearFPerfect_two_pow_mul_prime_pow 2 (a + 1) 0 (by decide) ⟨0, rfl⟩
    rw [pow_zero, mul_one, pow_succ, mul_comm] at h
    exact h ⟨d, hdvd, hlt, hsum⟩
  · have hpo : Odd p := hp.odd_of_ne_two h2
    obtain ⟨hdvd5, -⟩ := klNearPerfectWith_two_mul_prime_pow_imp p a 2 3 d hp hpo
      (by norm_num) (by norm_num) ⟨hdvd, hlt, hsum⟩
    norm_num at hdvd5
    have hle := Nat.le_of_dvd (by norm_num) hdvd5
    have hp3 : 3 ≤ p := by
      have h2le := hp.two_le
      omega
    have h9 : 9 ≤ p ^ 2 := by
      calc (9 : ℕ) = 3 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
    omega

end MathlibExt.NumberTheory.FkPerfectWanted
