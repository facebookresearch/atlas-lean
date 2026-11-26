/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FkPerfect
public import MathlibExt.NumberTheory.OddPrimeDeficientPerfect
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Deficient `F_k`-perfect numbers of the form `2 * p ^ a`

This module proves that `2 * p ^ a` is not deficient `F_k`-perfect (`IsDeficientFkPerfect`,
defined in `MathlibExt.NumberTheory.FkPerfect`) when `k > 2` and `p` is an odd prime.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia,
"On Near `F_k`-Perfect and Deficient `F_k`-Perfect Numbers", *INTEGERS* 25 (2025),
Article A86 (<https://math.colgate.edu/~integers/z86/z86.pdf>), Theorem 18.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **No deficient $F_k$-perfect number of the form $2p^a$ for $k > 2$.** Let $k > 2$, let $p$ be
an odd prime and let $a$ be a natural number. Then $2p^a$ is not deficient $F_k$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 18. -/
theorem not_isDeficientFkPerfect_two_mul_pow
    (k p a : ℕ) (hk : 2 < k) (hp : p.Prime) (hpo : Odd p) :
    ¬ IsDeficientFkPerfect k (2 * p ^ a) := by
  rintro ⟨d, hd, hlt, hsum⟩
  by_cases ha : a = 0
  · subst a
    simp only [pow_zero, mul_one] at hd hlt hsum
    have hd1 : d = 1 :=
      (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_right (Nat.ne_of_lt hlt)
    have h1 : (1 : ℕ) ∉ ({2} : Finset ℕ) := by decide
    simp only [hd1, Nat.prime_two.divisors, Finset.sum_insert h1,
      Finset.sum_singleton, one_pow] at hsum
    omega
  · have hq : 3 ≤ p ^ a := (hp.odd_iff.mp hpo).trans (Nat.le_self_pow ha p)
    have hn : 2 * p ^ a ≠ 0 := mul_ne_zero (by decide) (pow_ne_zero a hp.ne_zero)
    have hmem : p ^ a ∈ (2 * p ^ a).divisors :=
      Nat.mem_divisors.mpr ⟨dvd_mul_left (p ^ a) 2, hn⟩
    have hnmem : 2 * p ^ a ∈ (2 * p ^ a).divisors :=
      Nat.mem_divisors.mpr ⟨dvd_refl _, hn⟩
    have hne : p ^ a ≠ 2 * p ^ a := by omega
    have hbound : (p ^ a) ^ k + (2 * p ^ a) ^ k ≤
        ∑ e ∈ (2 * p ^ a).divisors, e ^ k :=
      Finset.add_le_sum (f := fun e => e ^ k) (fun _ _ => Nat.zero_le _) hmem hnmem hne
    have hcube : 9 * p ^ a ≤ (p ^ a) ^ 3 := by
      simpa only [← pow_succ] using
        Nat.mul_le_mul_right (p ^ a) (Nat.pow_le_pow_left hq 2)
    have hpow : (p ^ a) ^ 3 ≤ (p ^ a) ^ k :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega

end MathlibExt.NumberTheory.FkPerfectWanted
