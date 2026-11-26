/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import MathlibExt.NumberTheory.NearPerfectTwoPrimePower
public import MathlibExt.NumberTheory.OddPrimeDeficientPerfect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors

/-! # Near and deficient `F_k`-perfect numbers

Results from Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia, "On Near
`F_k`-Perfect and Deficient `F_k`-Perfect Numbers":

* `klDeficientPerfectWith_one_prime_pow_iff`: the prime power `p ^ a` is
  `[1,ℓ]`-deficient-perfect with divisor `d` if and only if `p = 2`, `ℓ = 1`, `d = 1` and
  `a ≥ 1`. This is the `k = 1` part of Theorem 5.
* `not_isNearFkPerfect_pow_mul_pow`: for distinct odd primes `p₁`, `p₂` and exponents
  `a, b ≥ 1` with `a + b` odd or both odd, `p₁ ^ a * p₂ ^ b` is not near `F_k`-perfect for
  `k > 1`: multiplicativity of the divisor sum `σₖ` factors it into geometric sums of `a + 1`
  and `b + 1` odd terms; as `a` or `b` is odd, one of these counts is even, so `σₖ` is even,
  while the near-perfect equation would force it to be odd (Theorem 20).

It also defines `IsKLNearPerfect` and `IsNearFkPerfect`.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

private theorem sum_range_two_pow_add_one (a : ℕ) :
    (∑ i ∈ Finset.range a, 2 ^ i) + 1 = 2 ^ a := by
  induction a with
  | zero => simp
  | succ a ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- **Prime powers that are $[1,\ell]$-deficient-perfect with a given divisor.** Let $p$ be a
prime, let $a$, $\ell$ and $d$ be natural numbers, and write $\sigma_1(m)$ for the sum of the
divisors of $m$. Then $d$ is a proper divisor of $p^a$ ($d \mid p^a$ and $d < p^a$) with
$\sigma_1(p^a) + d = p^a + \ell p^a$ if and only if $p = 2$, $\ell = 1$, $d = 1$ and $a \ge 1$.

This is the $k = 1$ part of Theorem 5 of the source.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 5. -/
theorem klDeficientPerfectWith_one_prime_pow_iff
    (p a l d : ℕ) (hp : p.Prime) :
    KLDeficientPerfectWith 1 l (p ^ a) d ↔
      p = 2 ∧ l = 1 ∧ d = 1 ∧ 1 ≤ a := by
  constructor
  · rintro ⟨hdvd, hlt, hsum⟩
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · rw [pow_zero] at hdvd hlt
        exact absurd (Nat.dvd_one.mp hdvd) (Nat.ne_of_lt hlt)
      · exact h
    obtain ⟨b, _hb, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hsigma : (∑ e ∈ (p ^ a).divisors, e) = ∑ i ∈ Finset.range (a + 1), p ^ i := by
      have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := p) (i := a) hp
      rwa [ArithmeticFunction.sigma_one_apply] at h
    simp only [pow_one] at hsum
    rw [hsigma] at hsum
    have htail : p ∣ ∑ i ∈ Finset.range a, p ^ (i + 1) := by
      apply Finset.dvd_sum
      intro i _
      exact dvd_pow_self p (by omega)
    have hpa0 : p ^ a ≡ 0 [MOD p] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self p (by omega))
    have hS1 : (∑ i ∈ Finset.range (a + 1), p ^ i) ≡ 1 [MOD p] := by
      rw [Finset.sum_range_succ', pow_zero]
      simpa only [zero_add] using
        (Nat.modEq_zero_iff_dvd.mpr htail).add (Nat.ModEq.refl 1)
    have hb0 : b = 0 := by
      by_contra hb
      have hpb0 : p ^ b ≡ 0 [MOD p] :=
        Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self p hb)
      have hleft : (∑ i ∈ Finset.range (a + 1), p ^ i) + p ^ b ≡ 1 [MOD p] := by
        simpa only [add_zero] using hS1.add hpb0
      have hright : p ^ a + l * p ^ a ≡ 0 [MOD p] := by
        simpa only [add_zero, mul_zero] using hpa0.add (hpa0.mul_left l)
      have hcongr : p ^ a + l * p ^ a ≡ 1 [MOD p] := by
        simpa only [hsum] using hleft
      have h10 : (1 : ℕ) ≡ 0 [MOD p] := hcongr.symm.trans hright
      exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp h10)
    have hd1 : p ^ b = 1 := by rw [hb0, pow_zero]
    rw [hd1] at hsum
    have hleft2 : (∑ i ∈ Finset.range (a + 1), p ^ i) + 1 ≡ 2 [MOD p] := by
      simpa only [one_add_one_eq_two] using hS1.add (Nat.ModEq.refl 1)
    have hright2 : p ^ a + l * p ^ a ≡ 0 [MOD p] := by
      simpa only [add_zero, mul_zero] using hpa0.add (hpa0.mul_left l)
    have hcongr2 : p ^ a + l * p ^ a ≡ 2 [MOD p] := by
      simpa only [hsum] using hleft2
    have hpdvd2 : p ∣ 2 := Nat.modEq_zero_iff_dvd.mp (hcongr2.symm.trans hright2)
    have hp2 : p = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hpdvd2 with h | h
      · exact absurd h hp.ne_one
      · exact h
    rw [hp2] at hsum
    have hsplit : (∑ i ∈ Finset.range (a + 1), (2 : ℕ) ^ i) =
        2 ^ a + ∑ i ∈ Finset.range a, 2 ^ i := by
      rw [Finset.sum_range_succ, add_comm]
    rw [hsplit] at hsum
    have hR := sum_range_two_pow_add_one a
    have hcancel : l * 2 ^ a = 1 * 2 ^ a := by omega
    have hpow_ne : (2 : ℕ) ^ a ≠ 0 := (pow_pos (by decide) a).ne'
    have hl1 : l = 1 := mul_right_cancel₀ hpow_ne hcancel
    exact ⟨hp2, hl1, hd1, ha⟩
  · rintro ⟨rfl, rfl, rfl, ha⟩
    refine ⟨one_dvd _, ?_, ?_⟩
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
      rw [pow_add, pow_one]
      have hpos : (0 : ℕ) < 2 ^ k := pow_pos (by decide) k
      omega
    · have hsigma : (∑ e ∈ ((2 : ℕ) ^ a).divisors, e) =
          ∑ i ∈ Finset.range (a + 1), 2 ^ i := by
        have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := 2) (i := a)
          Nat.prime_two
        rwa [ArithmeticFunction.sigma_one_apply] at h
      have hR := sum_range_two_pow_add_one a
      simp only [pow_one, one_mul]
      rw [hsigma, Finset.sum_range_succ]
      omega

/-- **$[k,\ell]$-near-perfect numbers.** For natural numbers $k$, $\ell$ and $n$, write
$\sigma_k(n) = \sum_{e \mid n} e^k$. The number $n$ is $[k,\ell]$-near-perfect when there is a
divisor $d$ of $n$ with $d < n$ such that $\sigma_k(n) = n^k + d^k + \ell n$. -/
def IsKLNearPerfect (k l n : ℕ) : Prop :=
  ∃ d, KLNearPerfectWith k l n d

/-- **Near $F_k$-perfect numbers.** For natural numbers $k$ and $n$, the number $n$ is near
$F_k$-perfect when it is $[k,3]$-near-perfect, that is, when some proper divisor $d$ of $n$
($d \mid n$ and $d < n$) satisfies $\sigma_k(n) = n^k + d^k + 3n$, where
$\sigma_k(n) = \sum_{e \mid n} e^k$ is the sum of the $k$-th powers of the divisors of $n$.

No condition $k > 1$ is imposed here; the results that need it assume it. -/
def IsNearFkPerfect (k n : ℕ) : Prop :=
  IsKLNearPerfect k 3 n

private theorem odd_prime_geom_sum_modEq_two (p b k : ℕ) (hpo : Odd p) :
    (∑ i ∈ Finset.range b, p ^ (i * k)) ≡ b [MOD 2] := by
  have hp1 : p ≡ 1 [MOD 2] := by
    simpa [Nat.ModEq] using Nat.odd_iff.mp hpo
  induction b with
  | zero =>
    simpa only [Finset.range_zero, Finset.sum_empty] using
      (Nat.ModEq.refl (n := 2) 0)
  | succ b ih =>
    rw [Finset.sum_range_succ]
    simpa only [one_pow, Nat.succ_eq_add_one] using ih.add (hp1.pow (b * k))

private theorem sigma_two_prime_pow (k p₁ p₂ a b : ℕ) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂) :
    (∑ e ∈ (p₁ ^ a * p₂ ^ b).divisors, e ^ k) =
      (∑ i ∈ Finset.range (a + 1), p₁ ^ (i * k)) *
        (∑ i ∈ Finset.range (b + 1), p₂ ^ (i * k)) := by
  have hcop : Nat.Coprime (p₁ ^ a) (p₂ ^ b) :=
    (((Nat.coprime_primes hp₁ hp₂).mpr hne).pow_left a).pow_right b
  rw [← ArithmeticFunction.sigma_apply,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    ArithmeticFunction.sigma_apply_prime_pow hp₁,
    ArithmeticFunction.sigma_apply_prime_pow hp₂]

/-- **No near $F_k$-perfect number $p_1^a p_2^b$ with $a + b$ odd or $a, b$ both odd.** Let
$k > 1$, let $p_1 \ne p_2$ be odd primes and let $a, b \ge 1$ be natural numbers such that
$a + b$ is odd or both $a$ and $b$ are odd. Then $p_1^a p_2^b$ is not near $F_k$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 20. -/
theorem not_isNearFkPerfect_pow_mul_pow
    (k p₁ p₂ a b : ℕ) (hk : 1 < k) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (ho₁ : Odd p₁) (ho₂ : Odd p₂)
    (hne : p₁ ≠ p₂) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hpar : Odd (a + b) ∨ (Odd a ∧ Odd b)) :
    ¬ IsNearFkPerfect k (p₁ ^ a * p₂ ^ b) := by
  -- The parity argument does not use `hk`, `ha` or `hb`; this keeps them referenced.
  have _nontrivial : k ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 := by omega
  rintro ⟨d, hdvd, _, hsum⟩
  have hnodd : Odd (p₁ ^ a * p₂ ^ b) := ho₁.pow.mul ho₂.pow
  have hdodd : Odd d := by
    by_contra hcon
    simp only [Nat.not_odd_iff_even] at hcon
    exact (Nat.not_even_iff_odd.mpr hnodd)
      (even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hcon).trans hdvd))
  have hodd_or : Odd a ∨ Odd b := by
    rcases hpar with h | ⟨ha', _⟩
    · by_contra hcon
      rw [not_or] at hcon
      simp only [Nat.not_odd_iff_even] at hcon
      exact (Nat.not_even_iff_odd.mpr h) (hcon.1.add hcon.2)
    · exact Or.inl ha'
  have heven_prod : Even ((a + 1) * (b + 1)) := by
    rcases hodd_or with ha' | hb'
    · exact (ha'.add_one).mul_right _
    · exact (hb'.add_one).mul_left _
  have hleft : (∑ e ∈ (p₁ ^ a * p₂ ^ b).divisors, e ^ k) ≡ 0 [MOD 2] := by
    rw [sigma_two_prime_pow k p₁ p₂ a b hp₁ hp₂ hne]
    exact ((odd_prime_geom_sum_modEq_two p₁ (a + 1) k ho₁).mul
      (odd_prime_geom_sum_modEq_two p₂ (b + 1) k ho₂)).trans
      (Nat.modEq_zero_iff_dvd.mpr (even_iff_two_dvd.mp heven_prod))
  have hevenL : Even (∑ e ∈ (p₁ ^ a * p₂ ^ b).divisors, e ^ k) := by
    rw [Nat.even_iff]
    simpa [Nat.ModEq] using hleft
  have hoddR : Odd ((p₁ ^ a * p₂ ^ b) ^ k + d ^ k + 3 * (p₁ ^ a * p₂ ^ b)) :=
    ((hnodd.pow).add_odd hdodd.pow).add_odd ((by decide : Odd 3).mul hnodd)
  rw [hsum] at hevenL
  exact (Nat.not_even_iff_odd.mpr hoddR) hevenL

end MathlibExt.NumberTheory.FkPerfectWanted
