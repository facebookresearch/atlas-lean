/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NearPerfectTwoPrimePower
import Mathlib.Algebra.Ring.Parity
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Near-perfect numbers of the form `2 ^ a * p`

For an odd prime `p` and `1 < a`, the number `2 ^ a * p` cannot be
`[k,ℓ]`-near-perfect with omitted divisor `1` or `p` when `1 ≤ ℓ`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia,
"On Near `F_k`-Perfect and Deficient `F_k`-Perfect Numbers", *INTEGERS* 25 (2025),
Article A86 (<https://math.colgate.edu/~integers/z86/z86.pdf>), Theorem 11.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

private theorem sigma_two_pow_mul (k p a : ℕ) (hp : p.Prime) (hpo : Odd p) :
    (∑ e ∈ (2 ^ a * p).divisors, e ^ k) =
      (∑ i ∈ Finset.range (a + 1), 2 ^ (i * k)) * (1 + p ^ k) := by
  have hprime : ArithmeticFunction.sigma k p = 1 + p ^ k := by
    simp [ArithmeticFunction.sigma_apply, hp.divisors, hp.ne_one.symm]
  rw [← ArithmeticFunction.sigma_apply,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
      ((Nat.coprime_two_left.mpr hpo).pow_left a),
    ArithmeticFunction.sigma_apply_prime_pow Nat.prime_two, hprime]

private theorem not_nearPerfect_odd (k l p a d : ℕ) (hl : 1 ≤ l) (hp : p.Prime)
    (hpo : Odd p) (ha : 1 < a) (hd : Odd d) :
    ¬ KLNearPerfectWith k l (2 ^ a * p) d := by
  rintro ⟨_, _, hsum⟩
  have hsigma := sigma_two_pow_mul k p a hp hpo
  by_cases hk : k = 0
  · subst k
    rw [hsigma] at hsum
    have hsum0 : 2 * (a + 1) = 2 + l * (2 ^ a * p) := by
      simpa [Nat.mul_comm] using hsum
    have hbound : 2 * (a + 1) ≤ l * (2 ^ a * p) := calc
      2 * (a + 1) ≤ 2 * 2 ^ a :=
        Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt Nat.lt_two_pow_self)
      _ ≤ 2 ^ a * p := by
        simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (2 ^ a) hp.two_le
      _ ≤ l * (2 ^ a * p) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · have he : Even (2 ^ a * p) :=
      (even_two.pow_of_ne_zero (by omega : a ≠ 0)).mul_right p
    have hleft : Even (∑ e ∈ (2 ^ a * p).divisors, e ^ k) := by
      rw [hsigma]
      exact (odd_one.add_odd hpo.pow).mul_left _
    have hright : Odd ((2 ^ a * p) ^ k + d ^ k + l * (2 ^ a * p)) :=
      ((he.pow_of_ne_zero hk).add_odd hd.pow).add_even (he.mul_left l)
    rw [hsum] at hleft
    exact (Nat.not_even_iff_odd.mpr hright) hleft

/-- **For $a \ge 2$, $2^a p$ is not $[k,\ell]$-near-perfect with divisor $1$ or $p$.** Let $k$,
$\ell$, $a$ be natural numbers with $\ell \ge 1$ and $a \ge 2$, and let $p$ be an odd prime. Call
$n$ $[k,\ell]$-near-perfect with divisor $d$ when $d$ divides $n$, $d < n$ and
$\sigma_k(n) = n^k + d^k + \ell n$, where $\sigma_k(n)$ is the sum of the $k$-th powers of the
divisors of $n$. Then $2^a p$ is not $[k,\ell]$-near-perfect with divisor $1$, and not with
divisor $p$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 11. -/
theorem not_klNearPerfectWith_two_pow_mul
    (k l p a : ℕ) (hl : 1 ≤ l) (hp : p.Prime) (hpo : Odd p)
    (ha : 1 < a) :
    ¬ KLNearPerfectWith k l (2 ^ a * p) 1 ∧
      ¬ KLNearPerfectWith k l (2 ^ a * p) p := by
  exact ⟨not_nearPerfect_odd k l p a 1 hl hp hpo ha odd_one,
    not_nearPerfect_odd k l p a p hl hp hpo ha hpo⟩

end MathlibExt.NumberTheory.FkPerfectWanted
