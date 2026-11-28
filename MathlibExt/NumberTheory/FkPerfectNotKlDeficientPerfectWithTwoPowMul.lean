/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.OddPrimeDeficientPerfect
import Mathlib.Algebra.Ring.Parity
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! # Deficient-perfect numbers of the form `2 ^ a * p`

For an odd prime `p` and `1 ≤ l`, the number `2 ^ a * p` is not
`[k,l]`-deficient-perfect with divisor `1` or `p`, including `k = 0` and `a = 0`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia,
"On Near `F_k`-Perfect and Deficient `F_k`-Perfect Numbers", *INTEGERS* 25 (2025),
Article A86 (<https://math.colgate.edu/~integers/z86/z86.pdf>), Theorem 8.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

private theorem not_klDeficientPerfectWith_odd_divisor
    (k l p a d : ℕ) (hl : 1 ≤ l) (hp : p.Prime) (hpo : Odd p) (hdo : Odd d) :
    ¬ KLDeficientPerfectWith k l (2 ^ a * p) d := by
  intro h
  by_cases ha : a = 0
  · exact not_isKLDeficientPerfect_of_prime_odd k l p hp hpo
      ⟨d, by simpa only [ha, pow_zero, one_mul] using h⟩
  have hcop := (Nat.coprime_two_left.mpr hpo).pow_left a
  have hprime : ArithmeticFunction.sigma k p = 1 + p ^ k := by
    simp [ArithmeticFunction.sigma_apply, hp.divisors, hp.ne_one.symm]
  have hsigma : (∑ e ∈ (2 ^ a * p).divisors, e ^ k) =
      (∑ i ∈ Finset.range (a + 1), 2 ^ (i * k)) * (1 + p ^ k) := by
    rw [← ArithmeticFunction.sigma_apply,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
      ArithmeticFunction.sigma_apply_prime_pow Nat.prime_two, hprime]
  have hsum := h.2.2
  rw [hsigma] at hsum
  by_cases hk : k = 0
  · subst k
    simp only [Nat.mul_zero, pow_zero, Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_one] at hsum
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      have := hp.odd_iff.mp hpo
      omega
    have hbound : a + 1 ≤ 2 ^ a := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := a))
    have hupper := Nat.mul_le_mul_right 2 hbound
    have hlower : 2 ^ a * 3 ≤ l * (2 ^ a * p) := calc
      2 ^ a * 3 ≤ 2 ^ a * p := Nat.mul_le_mul_left _ hp3
      _ ≤ l * (2 ^ a * p) := Nat.le_mul_of_pos_left _ (by omega)
    have hstrict : 2 ^ a * 2 < 2 ^ a * 3 :=
      Nat.mul_lt_mul_of_pos_left (by decide) (Nat.two_pow_pos a)
    omega
  · have hn : Even (2 ^ a * p) :=
      even_iff_two_dvd.mpr (dvd_mul_of_dvd_left (dvd_pow_self 2 ha) p)
    have hleft := ((hpo.pow (n := k)).one_add.mul_left
      (∑ i ∈ Finset.range (a + 1), 2 ^ (i * k))).add_odd (hdo.pow (n := k))
    have hright := (hn.pow_of_ne_zero hk).add (hn.mul_left l)
    rw [hsum] at hleft
    exact Nat.not_even_iff_odd.mpr hleft hright

/-- **$2^a p$ is not $[k,\ell]$-deficient-perfect with divisor $1$ or $p$.** Let $k$, $\ell$, $a$
be natural numbers with $\ell \ge 1$ and let $p$ be an odd prime. Call $n$
$[k,\ell]$-deficient-perfect with divisor $d$ when $d$ divides $n$, $d < n$ and
$\sigma_k(n) + d^k = n^k + \ell n$, where $\sigma_k(n)$ is the sum of the $k$-th powers of the
divisors of $n$. Then $2^a p$ is not $[k,\ell]$-deficient-perfect with divisor $1$, and not with
divisor $p$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 8. -/
theorem not_klDeficientPerfectWith_two_pow_mul
    (k l p a : ℕ) (hl : 1 ≤ l) (hp : p.Prime) (hpo : Odd p) :
    ¬ KLDeficientPerfectWith k l (2 ^ a * p) 1 ∧
      ¬ KLDeficientPerfectWith k l (2 ^ a * p) p := by
  exact ⟨not_klDeficientPerfectWith_odd_divisor k l p a 1 hl hp hpo (by decide),
    not_klDeficientPerfectWith_odd_divisor k l p a p hl hp hpo hpo⟩

end MathlibExt.NumberTheory.FkPerfectWanted
