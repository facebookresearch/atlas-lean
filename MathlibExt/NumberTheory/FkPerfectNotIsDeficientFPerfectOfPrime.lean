/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.OddPrimeDeficientPerfect

/-! # Deficient `F`-perfect numbers

This module defines deficient `F`-perfect numbers and proves that no prime is
deficient `F`-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia,
"On Near `F_k`-Perfect and Deficient `F_k`-Perfect Numbers", *INTEGERS* 25 (2025),
Article A86 (<https://math.colgate.edu/~integers/z86/z86.pdf>), Corollary 2.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **Deficient $F$-perfect numbers.** For a natural number $n$, write
$\sigma_2(n) = \sum_{e \mid n} e^2$. The number $n$ is deficient $F$-perfect when it is
$[2,3]$-deficient-perfect, that is, when there is a divisor $d$ of $n$ with $d < n$ such that
$\sigma_2(n) + d^2 = n^2 + 3n$. -/
def IsDeficientFPerfect (n : ℕ) : Prop :=
  IsKLDeficientPerfect 2 3 n

/-- **No prime is deficient $F$-perfect.** If $p$ is a prime, then $p$ is not deficient
$F$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Corollary 2. -/
theorem not_isDeficientFPerfect_of_prime (p : ℕ)
    (hp : p.Prime) :
    ¬ IsDeficientFPerfect p
    := by
  -- Divisor argument from `not_isKLDeficientPerfect_of_prime_odd` (OddPrimeDeficientPerfect.lean).
  rintro ⟨d, hd, hlt, hsum⟩
  have hdmem := Nat.mem_divisors.mpr ⟨hd, hp.ne_zero⟩
  rw [hp.divisors] at hdmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdmem
  have hd1 : d = 1 := hdmem.resolve_right fun he => (Nat.ne_of_lt hlt) he
  have h1 : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
    simpa only [Finset.mem_singleton] using hp.ne_one.symm
  simp only [hd1, hp.divisors, Finset.sum_insert h1, Finset.sum_singleton, one_pow] at hsum
  have hge := hp.two_le
  omega

end MathlibExt.NumberTheory.FkPerfectWanted
