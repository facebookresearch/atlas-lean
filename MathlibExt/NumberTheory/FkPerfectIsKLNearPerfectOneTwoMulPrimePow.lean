/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NearPerfectTwoPrimePower
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-! # Near-perfect numbers of the form `2 * p ^ a`

We define `[k,ell]`-near-perfect numbers and prove that the only `[1,ell]`-near-perfect
number of the form `2 * p ^ a`, for an odd prime `p` and positive `ell`, is `18`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia,
"On Near `F_k`-Perfect and Deficient `F_k`-Perfect Numbers", *INTEGERS* 25 (2025),
Article A86 (<https://math.colgate.edu/~integers/z86/z86.pdf>), Theorem 14, part 1.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **$[k,\ell]$-near-perfect numbers.** For natural numbers $k$, $\ell$ and $n$, write
$\sigma_k(n) = \sum_{e \mid n} e^k$. The number $n$ is $[k,\ell]$-near-perfect when there is a
divisor $d$ of $n$ with $d < n$ such that $\sigma_k(n) = n^k + d^k + \ell n$. -/
def IsKLNearPerfect (k l n : ℕ) : Prop :=
  ∃ d, KLNearPerfectWith k l n d

private theorem divisor_sum_two_mul_prime_pow (p a : ℕ) (hp : p.Prime) (hpo : Odd p) :
    (∑ e ∈ (2 * p ^ a).divisors, e ^ 1) =
      3 * ∑ i ∈ Finset.range (a + 1), p ^ i := by
  have htwo : ArithmeticFunction.sigma 1 2 = 3 := by
    simp [ArithmeticFunction.sigma_apply, Nat.prime_two.divisors]
  rw [← ArithmeticFunction.sigma_apply,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
      ((Nat.coprime_two_left.mpr hpo).pow_right a), htwo,
    ArithmeticFunction.sigma_apply_prime_pow hp]
  simp only [Nat.mul_one]

private theorem sum_three_pow_identity (a : ℕ) :
    2 * (∑ i ∈ Finset.range (a + 1), (3 : ℕ) ^ i) + 1 = 3 * 3 ^ a := by
  simpa [pow_succ, Nat.mul_comm] using geom_sum_mul_add (2 : ℕ) (a + 1)

private theorem nearPerfect_two_mul_prime_pow_eq (p a l d : ℕ)
    (hp : p.Prime) (hpo : Odd p) (hl : 1 ≤ l)
    (h : KLNearPerfectWith 1 l (2 * p ^ a) d) : 2 * p ^ a = 18 := by
  rcases h with ⟨hd, hlt, hsum⟩
  rw [divisor_sum_two_mul_prime_pow p a hp hpo] at hsum
  simp only [pow_one] at hsum
  have ha : a ≠ 0 := by
    intro ha
    subst a
    simp only [pow_zero, mul_one] at hd hlt hsum
    have hd1 : d = 1 :=
      (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_right (Nat.ne_of_lt hlt)
    have hs : 3 = 2 + d + l * 2 := by
      simpa only [Nat.zero_add, Finset.sum_range_one, pow_zero, mul_one] using hsum
    omega
  have hgeom : (∑ i ∈ Finset.range (a + 1), p ^ i) ≡ 1 [MOD p] := by
    rw [Finset.sum_range_succ', pow_zero]
    have htail : p ∣ ∑ i ∈ Finset.range a, p ^ (i + 1) := by
      apply Finset.dvd_sum
      intro i _
      exact dvd_pow_self p (by omega)
    simpa only [zero_add] using
      (Nat.modEq_zero_iff_dvd.mpr htail).add (Nat.ModEq.refl 1)
  have hn0 : 2 * p ^ a ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr
    (dvd_mul_of_dvd_right (dvd_pow_self p ha) 2)
  have hmod : 3 ≡ d [MOD p] := by
    have hleft := hgeom.mul_left 3
    rw [hsum] at hleft
    have hright : 2 * p ^ a + d + l * (2 * p ^ a) ≡ d [MOD p] := by
      simpa only [zero_add, mul_zero, add_zero] using
        (hn0.add (Nat.ModEq.refl d)).add (hn0.mul_left l)
    exact hleft.symm.trans hright
  have hpd : p ∣ d := by
    by_contra hnd
    have hd2 : d ∣ 2 := (hp.coprime_pow_of_not_dvd hnd).dvd_of_dvd_mul_right hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with rfl | rfl
    · have he : p ∣ 2 := Nat.modEq_zero_iff_dvd.mp
        ((Nat.ModEq.refl 1).add_iff_left.mp (by simpa using hmod))
      exact (hp.coprime_iff_not_dvd.mp (Nat.coprime_two_left.mpr hpo).symm) he
    · have he : p ∣ 1 := Nat.modEq_zero_iff_dvd.mp
        ((Nat.ModEq.refl 2).add_iff_right.mp (by simpa using hmod))
      exact hp.not_dvd_one he
  have hp3 : p = 3 := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp
    (Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr hpd)))
    |>.resolve_left hp.ne_one
  subst p
  have hqpos : 0 < (3 : ℕ) ^ a := pow_pos (by decide) a
  have hidentity : 2 * (∑ i ∈ Finset.range (a + 1), (3 : ℕ) ^ i) + 1 =
      3 * 3 ^ a := sum_three_pow_identity a
  have hl1 : l = 1 := by
    by_contra hne
    have hlarge : 2 * (2 * 3 ^ a) ≤ l * (2 * 3 ^ a) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith
  subst l
  have hq : 3 ^ a = 2 * d + 3 := by nlinarith
  have hd6 : d ∣ 6 := by
    have htwo : 2 * 3 ^ a = 4 * d + 6 := by omega
    have hdiv : d ∣ 4 * d + 6 := by simpa only [htwo] using hd
    exact (Nat.dvd_add_iff_right (dvd_mul_left d 4)).mpr hdiv
  have hdle : d ≤ 6 := Nat.le_of_dvd (by decide) hd6
  have hale : a ≤ 2 := by
    by_contra hna
    have hpow : (3 : ℕ) ^ 3 ≤ 3 ^ a := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at hpow
    omega
  interval_cases a
  · exact (ha rfl).elim
  · have hd0 : d = 0 := by
      simp only [pow_one] at hq
      omega
    subst d
    norm_num at hd
  · rfl

/-- **The only $[1,\ell]$-near-perfect number of the form $2p^a$ is $18$.** For natural numbers
$\ell$ and $n$, say that $n$ is $[1,\ell]$-near-perfect when some divisor $d$ of $n$ with $d < n$
satisfies $\sigma(n) = n + d + \ell n$, where $\sigma(n)$ is the sum of the divisors of $n$. Then
$18$ is $[1,1]$-near-perfect, and for every odd prime $p$ and all natural numbers $a$ and
$\ell \ge 1$, if $2p^a$ is $[1,\ell]$-near-perfect then $2p^a = 18$.

The divisor for $18$ is $d = 3$. This is part 1 of Theorem 14 of the source.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 14. -/
theorem isKLNearPerfect_one_two_mul_prime_pow
    (p a l : ℕ) (hp : p.Prime) (hpo : Odd p) (hl : 1 ≤ l) :
    IsKLNearPerfect 1 1 18 ∧
      (IsKLNearPerfect 1 l (2 * p ^ a) → 2 * p ^ a = 18)
    := by
  refine ⟨?_, ?_⟩
  · refine ⟨3, ?_⟩
    unfold KLNearPerfectWith
    decide
  · rintro ⟨d, hd⟩
    exact nearPerfect_two_mul_prime_pow_eq p a l d hp hpo hl hd

end MathlibExt.NumberTheory.FkPerfectWanted
