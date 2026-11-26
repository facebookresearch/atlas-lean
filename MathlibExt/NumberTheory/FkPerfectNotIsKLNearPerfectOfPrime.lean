/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NearPerfectTwoPrimePower

/-! # Primes and near-perfect numbers

This module defines `[k,ℓ]`-near-perfect numbers and proves that primes are not
`[k,ℓ]`-near-perfect when `1 ≤ ℓ`, for every natural exponent `k`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia,
"On Near `F_k`-Perfect and Deficient `F_k`-Perfect Numbers", *INTEGERS* 25 (2025),
Article A86 (<https://math.colgate.edu/~integers/z86/z86.pdf>), Proposition 2.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **$[k,\ell]$-near-perfect numbers.** For natural numbers $k$, $\ell$ and $n$, write
$\sigma_k(n) = \sum_{e \mid n} e^k$. The number $n$ is $[k,\ell]$-near-perfect when there is a
divisor $d$ of $n$ with $d < n$ such that $\sigma_k(n) = n^k + d^k + \ell n$. -/
def IsKLNearPerfect (k l n : ℕ) : Prop :=
  ∃ d, KLNearPerfectWith k l n d

/-- **Primes are not $[k,\ell]$-near-perfect.** Let $k$ and $\ell$ be natural numbers with
$\ell \ge 1$ and let $p$ be a prime. Then $p$ is not $[k,\ell]$-near-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Proposition 2. -/
theorem not_isKLNearPerfect_of_prime (k l p : ℕ)
    (hl : 1 ≤ l) (hp : p.Prime) :
    ¬ IsKLNearPerfect k l p := by
  rintro ⟨d, hd, hlt, hsum⟩
  have hd1 : d = 1 := (Nat.dvd_prime hp).mp hd |>.resolve_right (Nat.ne_of_lt hlt)
  rw [hp.sum_divisors, hd1, one_pow] at hsum
  have hzero : l * p = 0 := Nat.add_left_cancel (hsum.symm.trans (Nat.add_zero _).symm)
  exact (Nat.ne_of_gt (Nat.mul_pos (Nat.succ_le_iff.mp hl) hp.pos)) hzero

end MathlibExt.NumberTheory.FkPerfectWanted
