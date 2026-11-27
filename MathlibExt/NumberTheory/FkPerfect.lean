/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.NumberTheory.NearPerfectTwoPrimePower
public import MathlibExt.NumberTheory.OddPrimeDeficientPerfect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-! # Near and deficient `F_k`-perfect numbers

Results from Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia,
"On Near `F_k`-Perfect and Deficient `F_k`-Perfect Numbers", *INTEGERS* 25 (2025),
Article A86 (<https://math.colgate.edu/~integers/z86/z86.pdf>).

## Main statements

* `isKLDeficientPerfect_prime_pow_two_iff`: for a prime `p`, the prime power `p ^ a` is
  `[2,ℓ]`-deficient-perfect exactly when `p = 2`, `a = 1` and `ℓ = 1`. Reducing the
  divisor-sum equation modulo `p ^ 2` excludes every exponent `a ≥ 2`, and at `a = 1` the
  equation gives `ℓ * p = 2`. The weaker form that also allows `a = 2` is
  `isKLDeficientPerfect_prime_pow_two_imp` (Theorem 3, corrected by the solution `2` of
  Corollary 1).
* `klDeficientPerfectWith_one_prime_pow_iff`: the prime power `p ^ a` is
  `[1,ℓ]`-deficient-perfect with divisor `d` if and only if `p = 2`, `ℓ = 1`, `d = 1` and
  `a ≥ 1`. This is the `k = 1` part of Theorem 5.
* `not_isKLNearPerfect_of_prime`: for `1 ≤ ℓ`, no prime is `[k,ℓ]`-near-perfect: its only
  proper divisor is `1`, which leaves `ℓ * p = 0` (Proposition 2).
* `isKLNearPerfect_one_two_mul_prime_pow`: `18` is `[1,1]`-near-perfect, and for an odd prime
  `p` and `1 ≤ ℓ`, the only `[1,ℓ]`-near-perfect number of the form `2 * p ^ a` is `18`
  (Theorem 14, part 1).
* `not_isNearFPerfect_two_pow_mul_prime_pow`: for a prime `p` and even `b`, the number
  `2 ^ a * p ^ b` is not near `F`-perfect: no proper divisor `d` satisfies
  `σ₂(n) = n ^ 2 + d ^ 2 + 3 * n` (Theorem 15). Prime powers are excluded by reducing the
  divisor-sum equation modulo `p ^ 2`. For odd `p` with both exponents positive, the four
  divisors `1`, `n / 2`, `n / p` and `n` force `n < 3 * p ^ 2`, leaving only `n = 2 * p ^ 2`,
  which is excluded by squeezing `d` between consecutive squares.
* `not_isNearFkPerfect_prime_pow_mul`: for `k > 1` and distinct odd primes `p₁` and `p₂`, no
  number `p₁ ^ a * p₂` is near `F_k`-perfect (Theorem 17). Multiplicativity gives
  `σₖ(n) = σₖ(p₁ ^ a) * (1 + p₂ ^ k)`, which is even, while `n ^ k + d ^ k + 3 * n` is odd.
* `not_isDeficientFkPerfect_prod_primes`: for `k > 1` and a finite set `s` of odd primes,
  `∏ p ∈ s, p` is not deficient `F_k`-perfect (Theorem 21).
* `not_isDeficientFkPerfect_pow_mul_pow`: for `k > 1`, distinct odd primes `p₁` and `p₂` and
  exponents `a, b ≥ 1` with `a + b` odd or both `a` and `b` odd, the number `p₁ ^ a * p₂ ^ b` is
  not deficient `F_k`-perfect (Theorem 19). Every divisor is odd and the divisor count
  `(a + 1) * (b + 1)` is even, so `σₖ(n) + d ^ k` is odd while `n ^ k + 3 * n` is even.
* `not_isDeficientFkPerfect_prime_pow_mul`: for `k > 1` and distinct odd primes `p₁` and `p₂`,
  no number `p₁ ^ a * p₂` is deficient `F_k`-perfect (Theorem 16). Its divisors are all odd and
  even in number, so `σₖ(n) + d ^ k` is odd while `n ^ k + 3 * n` is even.
* `klNearPerfectWith_prime_pow_iff`: for `k ≥ 1` and `ℓ ≥ 1`, the prime power `p ^ a` is
  `[k,ℓ]`-near-perfect with divisor `d` if and only if `2 ≤ a ≤ k`, `d = 1` and
  `ℓ = p ^ (k - a) * ∑ i ∈ Finset.range (a - 1), p ^ (i * k)`. This is Theorem 4, whose printed
  conclusion `a = k` is false in general.
* `not_isNearFkPerfect_pow_mul_pow`: for distinct odd primes `p₁`, `p₂` and exponents
  `a, b ≥ 1` with `a + b` odd or both odd, `p₁ ^ a * p₂ ^ b` is not near `F_k`-perfect for
  `k > 1`: multiplicativity of the divisor sum `σₖ` factors it into geometric sums of `a + 1`
  and `b + 1` odd terms; as `a` or `b` is odd, one of these counts is even, so `σₖ` is even,
  while the near-perfect equation would force it to be odd (Theorem 20).

It also defines `IsKLNearPerfect`, `IsNearFPerfect` and `IsNearFkPerfect`.
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

private theorem geom_two_modEq (p a : ℕ) :
    (∑ i ∈ Finset.range (a + 1), p ^ (i * 2)) ≡ 1 [MOD p ^ 2] := by
  rw [Finset.sum_range_succ', Nat.zero_mul, pow_zero]
  have htail : p ^ 2 ∣ ∑ i ∈ Finset.range a, p ^ ((i + 1) * 2) := by
    apply Finset.dvd_sum
    intro i _
    exact Nat.pow_dvd_pow p (show 2 ≤ (i + 1) * 2 by omega)
  simpa only [zero_add] using
    (Nat.modEq_zero_iff_dvd.mpr htail).add (Nat.ModEq.refl 1)

private theorem range_one_add_one_sum (p : ℕ) :
    (∑ i ∈ Finset.range (1 + 1), p ^ (i * 2)) = 1 + p ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp

/-- **$[2,\ell]$-deficient-perfect prime powers (corrected).** Let $p$ be a prime and let $a$ and
$\ell$ be natural numbers. If $p^a$ is $[2,\ell]$-deficient-perfect, then $\ell = 1$, and either
$a = 2$, or $p = 2$ and $a = 1$.

The printed statement allows only the exception $a = 2$, $\ell = 1$, and so omits the solution
$p = 2$, $a = 1$, $\ell = 1$, $d = 1$ (the number $2$ of Corollary 1).

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 3. -/
theorem isKLDeficientPerfect_prime_pow_two_imp
    (p a l : ℕ) (hp : p.Prime) :
    IsKLDeficientPerfect 2 l (p ^ a) →
      l = 1 ∧ (a = 2 ∨ (p = 2 ∧ a = 1)) := by
  rintro ⟨d, hd, hlt, hsum⟩
  have hS : (∑ e ∈ (p ^ a).divisors, e ^ 2)
      = ∑ i ∈ Finset.range (a + 1), p ^ (i * 2) := by
    rw [← ArithmeticFunction.sigma_apply,
      ArithmeticFunction.sigma_apply_prime_pow hp]
  rw [hS] at hsum
  obtain ⟨b, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
  have hba_lt : b < a := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
  have ha1 : 1 ≤ a := by omega
  by_cases ha2 : 2 ≤ a
  · exfalso
    have hgeom : (∑ i ∈ Finset.range (a + 1), p ^ (i * 2)) ≡ 1 [MOD p ^ 2] :=
      geom_two_modEq p a
    have hpow1 : p ^ 2 ∣ (p ^ a) ^ 2 := by
      rw [← pow_mul]
      exact Nat.pow_dvd_pow p (show 2 ≤ a * 2 by omega)
    have hpow2 : p ^ 2 ∣ l * p ^ a :=
      (Nat.pow_dvd_pow p ha2).trans (dvd_mul_left _ _)
    have hmod : (∑ i ∈ Finset.range (a + 1), p ^ (i * 2)) + (p ^ b) ^ 2
        ≡ 0 [MOD p ^ 2] := by
      rw [hsum]
      simpa only [add_zero] using
        (Nat.modEq_zero_iff_dvd.mpr hpow1).add (Nat.modEq_zero_iff_dvd.mpr hpow2)
    have h1 : (1 : ℕ) + (p ^ b) ^ 2 ≡ 0 [MOD p ^ 2] :=
      (hgeom.add (Nat.ModEq.refl ((p ^ b) ^ 2))).symm.trans hmod
    have hdvd : p ^ 2 ∣ 1 + (p ^ b) ^ 2 := Nat.modEq_zero_iff_dvd.mp h1
    rw [← pow_mul] at hdvd
    have h4 : (4 : ℕ) ≤ p ^ 2 := by
      have h := Nat.pow_le_pow_left hp.two_le 2
      rwa [show (2 : ℕ) ^ 2 = 4 by decide] at h
    by_cases hb0 : b = 0
    · subst hb0
      rw [zero_mul, pow_zero] at hdvd
      have hle := Nat.le_of_dvd (by decide : 0 < 1 + 1) hdvd
      omega
    · have hpb : p ^ 2 ∣ p ^ (b * 2) :=
        Nat.pow_dvd_pow p (show 2 ≤ b * 2 by omega)
      have h1dvd : p ^ 2 ∣ 1 := by
        have hsub := Nat.dvd_sub hdvd hpb
        rwa [Nat.add_sub_cancel] at hsub
      have hle := Nat.le_of_dvd (by decide : 0 < 1) h1dvd
      omega
  · have ha1' : a = 1 := by omega
    subst ha1'
    rw [range_one_add_one_sum] at hsum
    have hb0 : b = 0 := by omega
    subst hb0
    simp only [pow_zero, pow_one, one_pow] at hsum
    have hlp : l * p = 2 := by omega
    have hdiv : p ∣ 2 := ⟨l, hlp.symm.trans (Nat.mul_comm l p)⟩
    have hp2 : p = 2 :=
      ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left hp.ne_one
    subst hp2
    have hl1 : l = 1 := by omega
    exact ⟨hl1, Or.inr ⟨rfl, rfl⟩⟩

/-- **$[2,\ell]$-deficient-perfect prime powers, classified.** Let $p$ be a prime and let $a$ and
$\ell$ be natural numbers. Then $p^a$ is $[2,\ell]$-deficient-perfect if and only if $p = 2$,
$a = 1$ and $\ell = 1$.

The printed statement allows the exception $a = 2$, $\ell = 1$ and omits the number $2$. The
exception does not occur, and $2$ is $[2,1]$-deficient-perfect by Corollary 1.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 3 and Corollary 1. -/
theorem isKLDeficientPerfect_prime_pow_two_iff (p a l : ℕ) (hp : p.Prime) :
    IsKLDeficientPerfect 2 l (p ^ a) ↔ p = 2 ∧ a = 1 ∧ l = 1 := by
  constructor
  · intro h
    obtain ⟨rfl, ha⟩ := isKLDeficientPerfect_prime_pow_two_imp p a l hp h
    rcases ha with rfl | ⟨rfl, rfl⟩
    · exfalso
      obtain ⟨d, -, -, hsum⟩ := h
      rw [← ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply_prime_pow hp] at hsum
      simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsum
      ring_nf at hsum
      omega
    · exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simpa using isKLDeficientPerfect_two 2

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

/-- **Near $F$-perfect numbers.** A natural number $n$ is near $F$-perfect when it is
$[2,3]$-near-perfect, that is, when some proper divisor $d$ of $n$ ($d \mid n$ and $d < n$)
satisfies $\sigma_2(n) = n^2 + d^2 + 3n$, where $\sigma_2(n) = \sum_{e \mid n} e^2$ is the sum
of the squares of the divisors of $n$. -/
def IsNearFPerfect (n : ℕ) : Prop :=
  IsKLNearPerfect 2 3 n

private theorem geom_sum_peel (p n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), p ^ (i * 2))
      = p ^ 2 * (∑ i ∈ Finset.range n, p ^ (i * 2)) + 1 := by
  rw [Finset.sum_range_succ']
  simp only [Nat.zero_mul, pow_zero]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hexp : (i + 1) * 2 = i * 2 + 2 := by ring
  rw [hexp, pow_add]
  exact mul_comm _ _

private theorem not_isNearFPerfect_prime_pow (p m : ℕ) (hp : p.Prime) :
    ¬ IsNearFPerfect (p ^ m) := by
  rintro ⟨d, hdvd, hlt, hsum⟩
  obtain ⟨t, htm_le, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have htm : t < m :=
    lt_of_le_of_ne htm_le fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
  have hm1 : 1 ≤ m := by omega
  have hsigma : (∑ e ∈ (p ^ m).divisors, e ^ 2)
      = ∑ i ∈ Finset.range (m + 1), p ^ (i * 2) := by
    rw [← ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply_prime_pow hp]
  rw [hsigma, Finset.sum_range_succ, ← pow_mul p m 2, ← pow_mul p t 2] at hsum
  have hbase : (∑ i ∈ Finset.range m, p ^ (i * 2)) = p ^ (t * 2) + 3 * p ^ m := by
    omega
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [geom_sum_peel] at hbase
  by_cases ht : t = 0
  · subst ht
    simp only [Nat.zero_mul, pow_zero] at hbase
    have hpeq : p ^ 2 * (∑ i ∈ Finset.range m', p ^ (i * 2)) = 3 * p ^ (m' + 1) := by
      omega
    by_cases hm' : m' = 0
    · subst hm'
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add,
        pow_one] at hpeq
      have hp0 := hp.ne_zero
      omega
    · have hm'1 : 1 ≤ m' := Nat.one_le_iff_ne_zero.mpr hm'
      have hcancel : (∑ i ∈ Finset.range m', p ^ (i * 2)) = 3 * p ^ (m' - 1) := by
        have h2 : p ^ (m' + 1) = p ^ 2 * p ^ (m' - 1) := by
          rw [← pow_add]
          congr 1
          omega
        rw [h2] at hpeq
        have h3 : p ^ 2 * (∑ i ∈ Finset.range m', p ^ (i * 2))
            = p ^ 2 * (3 * p ^ (m' - 1)) := by rw [hpeq]; ring
        exact Nat.mul_left_cancel (pow_pos hp.pos 2) h3
      by_cases hm'1eq : m' = 1
      · subst hm'1eq
        simp at hcancel
      · have hm'2 : 2 ≤ m' := by omega
        obtain ⟨m'', rfl⟩ : ∃ m'', m' = m'' + 1 := ⟨m' - 1, by omega⟩
        rw [geom_sum_peel] at hcancel
        simp only [Nat.add_sub_cancel] at hcancel
        have hdvd : p ∣ 3 * p ^ m'' :=
          dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) 3
        have hR : 3 * p ^ m'' ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hdvd
        have hL : p ^ 2 * (∑ i ∈ Finset.range m'', p ^ (i * 2)) + 1 ≡ 1 [MOD p] := by
          have e : p ^ 2 * (∑ i ∈ Finset.range m'', p ^ (i * 2)) + 1
              = 1 + p * (p * (∑ i ∈ Finset.range m'', p ^ (i * 2))) := by ring
          rw [e]
          exact (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right p _)).add_left 1
        rw [hcancel] at hL
        exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp (hL.symm.trans hR))
  · have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht
    have hm'1 : 1 ≤ m' := by omega
    have hR0 : p ^ (t * 2) + 3 * p ^ (m' + 1) ≡ 0 [MOD p ^ 2] := by
      apply Nat.modEq_zero_iff_dvd.mpr
      have e1 : p ^ (t * 2) = p ^ 2 * p ^ (t * 2 - 2) := by
        rw [← pow_add]
        congr 1
        omega
      have e2 : p ^ (m' + 1) = p ^ 2 * p ^ (m' + 1 - 2) := by
        rw [← pow_add]
        congr 1
        omega
      have e3 : 3 * p ^ (m' + 1) = p ^ 2 * (3 * p ^ (m' + 1 - 2)) := by
        rw [e2]; ring
      rw [e1, e3, ← mul_add]
      exact dvd_mul_right _ _
    have hL1 : p ^ 2 * (∑ i ∈ Finset.range m', p ^ (i * 2)) + 1 ≡ 1 [MOD p ^ 2] := by
      have e : p ^ 2 * (∑ i ∈ Finset.range m', p ^ (i * 2)) + 1
          = 1 + p ^ 2 * (∑ i ∈ Finset.range m', p ^ (i * 2)) := by ring
      rw [e]
      exact (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)).add_left 1
    rw [hbase] at hL1
    have hcontra : (1 : ℕ) ≡ 0 [MOD p ^ 2] := hL1.symm.trans hR0
    have hle : p ^ 2 ≤ 1 :=
      Nat.le_of_dvd (by decide) (Nat.modEq_zero_iff_dvd.mp hcontra)
    have hge : 4 ≤ p ^ 2 := by
      have h := Nat.pow_le_pow_left hp.two_le 2
      norm_num at h
      exact h
    omega

/-- **No near $F$-perfect number of the form $2^a p^b$ with $b$ even.** For every prime $p$ and
all natural numbers $a$ and $b$ with $b$ even, the number $n = 2^a p^b$ is not near $F$-perfect:
there is no divisor $d$ of $n$ with $d < n$ and $\sigma_2(n) = n^2 + d^2 + 3n$, where
$\sigma_2(n)$ is the sum of the squares of the divisors of $n$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 15. -/
theorem not_isNearFPerfect_two_pow_mul_prime_pow
    (p a b : ℕ) (hp : p.Prime) (hb : Even b) :
    ¬ IsNearFPerfect (2 ^ a * p ^ b) := by
  rintro ⟨d, hdvd, hlt, hsum⟩
  by_cases ha : a = 0
  · subst ha
    simp only [pow_zero, one_mul] at hdvd hlt hsum
    exact not_isNearFPerfect_prime_pow p b hp ⟨d, hdvd, hlt, hsum⟩
  by_cases hb0 : b = 0
  · subst hb0
    simp only [pow_zero, mul_one] at hdvd hlt hsum
    exact not_isNearFPerfect_prime_pow 2 a Nat.prime_two ⟨d, hdvd, hlt, hsum⟩
  rcases hp.eq_two_or_odd with rfl | hmod
  · rw [← pow_add] at hdvd hlt hsum
    exact not_isNearFPerfect_prime_pow 2 (a + b) Nat.prime_two ⟨d, hdvd, hlt, hsum⟩
  · have hpo : Odd p := Nat.odd_iff.mpr hmod
    have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
    have hb2 : 2 ≤ b := by
      obtain ⟨r, hr⟩ := hb
      omega
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
    have hne2 : p ≠ 2 := by
      rintro rfl
      omega
    have hp2le := hp.two_le
    have hp3 : 3 ≤ p := by omega
    have hpp := hp.pos
    set n := 2 ^ (a' + 1) * p ^ (b' + 2) with hn
    have hnpos : 0 < n := by
      rw [hn]
      positivity
    have hn0 : n ≠ 0 := ne_of_gt hnpos
    have h2a : 2 ≤ 2 ^ (a' + 1) := by
      have h := pow_le_pow_right₀ (show (1 : ℕ) ≤ 2 by decide) (show 1 ≤ a' + 1 by omega)
      simpa using h
    have hp2_ge : 9 ≤ p ^ 2 := by
      simpa using Nat.pow_le_pow_left hp3 2
    have h1 : p ^ 2 ≤ p ^ (b' + 2) :=
      pow_le_pow_right₀ (show (1 : ℕ) ≤ p by omega) (show 2 ≤ b' + 2 by omega)
    have hpb : 9 ≤ p ^ (b' + 2) := le_trans hp2_ge h1
    have hn18 : 18 ≤ n := by
      rw [hn]
      simpa using Nat.mul_le_mul h2a hpb
    have h2dvd : 2 ∣ n := by
      rw [hn]
      exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
    have hpdvd : p ∣ n := by
      rw [hn]
      exact dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) _
    have hhalf : n / 2 * 2 = n := Nat.div_mul_cancel h2dvd
    have hdivp : n / p * p = n := Nat.div_mul_cancel hpdvd
    have hdvd_half : n / 2 ∣ n := ⟨2, hhalf.symm⟩
    have hdvd_divp : n / p ∣ n := ⟨p, hdivp.symm⟩
    have h1n : 1 < n := by omega
    have hhalf_lt : n / 2 < n := Nat.div_lt_self hnpos (by decide)
    have hdivp_lt : n / p < n := Nat.div_lt_self hnpos (show 1 < p by omega)
    have h1_half : 1 < n / 2 := by omega
    have hn_eq : n = p * (2 ^ (a' + 1) * p ^ (b' + 1)) := by
      rw [hn]
      have hexp : p ^ (b' + 2) = p * p ^ (b' + 1) := by
        rw [show b' + 2 = 1 + (b' + 1) from by omega, pow_add, pow_one]
      rw [hexp]
      ring
    have g2 : 3 ≤ p ^ (b' + 1) := by
      have h := pow_le_pow_right₀ (show (1 : ℕ) ≤ p by omega) (show 1 ≤ b' + 1 by omega)
      rw [pow_one] at h
      omega
    have hM6 : 6 ≤ 2 ^ (a' + 1) * p ^ (b' + 1) := by
      simpa using Nat.mul_le_mul h2a g2
    have hnp_eq : n / p = 2 ^ (a' + 1) * p ^ (b' + 1) := by
      rw [hn_eq]
      exact Nat.mul_div_cancel_left _ hp.pos
    have h1_divp : 1 < n / p := by
      rw [hnp_eq]
      omega
    have hne_half_divp : n / 2 ≠ n / p := by
      intro h
      rw [← h] at hdivp
      have h2eq : (2 : ℕ) = p :=
        Nat.mul_left_cancel (show 0 < n / 2 by omega) (by rw [hhalf, hdivp])
      rw [← h2eq] at hpo
      omega
    have hsub : ({1, n / 2, n / p, n} : Finset ℕ) ⊆ n.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Nat.mem_divisors.mpr ⟨one_dvd n, hn0⟩
      · exact Nat.mem_divisors.mpr ⟨hdvd_half, hn0⟩
      · exact Nat.mem_divisors.mpr ⟨hdvd_divp, hn0⟩
      · exact Nat.mem_divisors.mpr ⟨dvd_rfl, hn0⟩
    have g1 : (1 : ℕ) ∉ ({n / 2, n / p, n} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ne_of_lt h1_half, ne_of_lt h1_divp, ne_of_lt h1n⟩
    have g2' : n / 2 ∉ ({n / p, n} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne_half_divp, ne_of_lt hhalf_lt⟩
    have g3 : n / p ∉ ({n} : Finset ℕ) := by
      simp only [Finset.mem_singleton]
      exact ne_of_lt hdivp_lt
    have hle : (∑ e ∈ ({1, n / 2, n / p, n} : Finset ℕ), e ^ 2)
        ≤ ∑ e ∈ n.divisors, e ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => Nat.zero_le _)
    simp only [Finset.sum_insert g1, Finset.sum_insert g2', Finset.sum_insert g3,
      Finset.sum_singleton, one_pow] at hle
    obtain ⟨m, hm⟩ := hdvd
    have hd1 : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with rfl | hpos
      · rw [zero_mul] at hm
        exact absurd hm hn0
      · exact hpos
    have hm2 : 2 ≤ m := by
      by_contra h
      push Not at h
      have h01 : m = 0 ∨ m = 1 := by omega
      rcases h01 with rfl | rfl
      · rw [mul_zero] at hm
        exact hn0 hm
      · rw [mul_one] at hm
        omega
    have h2d : d * 2 ≤ n := by
      rw [hm]
      exact Nat.mul_le_mul_left d hm2
    have hd_half : d ≤ n / 2 := (Nat.le_div_iff_mul_le (by decide)).mpr h2d
    have hd2sq : d ^ 2 ≤ (n / 2) ^ 2 := Nat.pow_le_pow_left hd_half 2
    have hstep : 1 + (n / p) ^ 2 ≤ 3 * n := by omega
    have hsq : (n / p) ^ 2 * p ^ 2 = n ^ 2 := by
      have e : (n / p) ^ 2 * p ^ 2 = (n / p * p) ^ 2 := by ring
      rw [e, hdivp]
    have hmul : p ^ 2 + n ^ 2 ≤ 3 * n * p ^ 2 := by
      have h := Nat.mul_le_mul_right (p ^ 2) hstep
      have e : (1 + (n / p) ^ 2) * p ^ 2 = p ^ 2 + n ^ 2 := by
        rw [add_mul, one_mul, hsq]
      rw [e] at h
      exact h
    have hp2pos : 0 < p ^ 2 := pow_pos hp.pos 2
    have hnlt : n < 3 * p ^ 2 := by
      by_contra hcon
      push Not at hcon
      have hle2 : (3 * p ^ 2) * n ≤ n * n := Nat.mul_le_mul_right n hcon
      have e1 : (3 * p ^ 2) * n = 3 * n * p ^ 2 := by ring
      have e2 : n * n = n ^ 2 := by ring
      rw [e1, e2] at hle2
      omega
    have hpb_le : p ^ (b' + 2) ≤ n := by
      rw [hn]
      exact Nat.le_mul_of_pos_left _ (by positivity)
    have hplt3 : p ^ b' < 3 := by
      have hexp : p ^ (b' + 2) = p ^ b' * p ^ 2 := pow_add p b' 2
      rw [hexp] at hpb_le
      have h2 : p ^ b' * p ^ 2 < 3 * p ^ 2 := lt_of_le_of_lt hpb_le hnlt
      exact lt_of_mul_lt_mul_right h2 (Nat.zero_le _)
    have hb'_eq : b' = 0 := by
      by_contra h
      have hc1 : 1 ≤ b' := Nat.one_le_iff_ne_zero.mpr h
      have hpow := pow_le_pow_right₀ (show (1 : ℕ) ≤ p by omega) hc1
      rw [pow_one] at hpow
      omega
    subst hb'_eq
    have hn2 : n = 2 ^ (a' + 1) * p ^ 2 := by
      rw [hn]
    have halt3 : 2 ^ (a' + 1) < 3 := by
      rw [hn2] at hnlt
      exact lt_of_mul_lt_mul_right hnlt (Nat.zero_le _)
    have ha'_eq : a' = 0 := by
      by_contra h
      have hc1 : 1 ≤ a' := Nat.one_le_iff_ne_zero.mpr h
      have hpow := pow_le_pow_right₀ (show (1 : ℕ) ≤ 2 by decide) (show 2 ≤ a' + 1 by omega)
      norm_num at hpow
      omega
    subst ha'_eq
    have hnfinal : n = 2 * p ^ 2 := by
      rw [hn]
      norm_num
    rw [hnfinal] at hsum
    have hcop : Nat.Coprime 2 (p ^ 2) := (Nat.coprime_two_left.mpr hpo).pow_right 2
    have hsigma : (∑ e ∈ (2 * p ^ 2).divisors, e ^ 2)
        = (1 + 2 ^ 2) * ∑ i ∈ Finset.range (2 + 1), p ^ (i * 2) := by
      have htwo : ArithmeticFunction.sigma 2 2 = 1 + 2 ^ 2 := by
        simp [ArithmeticFunction.sigma_apply, Nat.prime_two.divisors]
      rw [← ArithmeticFunction.sigma_apply,
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        htwo, ArithmeticFunction.sigma_apply_prime_pow hp]
    have hS : (∑ i ∈ Finset.range (2 + 1), p ^ (i * 2)) = 1 + p ^ 2 + p ^ 4 := by
      rw [show Finset.range (2 + 1) = ({0, 1, 2} : Finset ℕ) from by decide]
      simp only [Finset.sum_insert (by decide : (0 : ℕ) ∉ ({1, 2} : Finset ℕ)),
        Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ)), Finset.sum_singleton]
      norm_num
      ring
    rw [hsigma, hS] at hsum
    have heq : d ^ 2 + p ^ 2 = p ^ 4 + 5 := by
      have e1 : (1 + 2 ^ 2) * (1 + p ^ 2 + p ^ 4) = 5 + 5 * p ^ 2 + 5 * p ^ 4 := by ring
      have e2 : (2 * p ^ 2) ^ 2 = 4 * p ^ 4 := by ring
      rw [e1, e2] at hsum
      omega
    have h5 : 5 < p ^ 2 := by omega
    have hA : d ^ 2 < p ^ 4 := by omega
    have hB : (p ^ 2 - 1) ^ 2 < d ^ 2 := by
      have hexpand : (p ^ 2 - 1) * (p ^ 2 - 1) + 2 * p ^ 2 = p ^ 4 + 1 := by
        have e : p ^ 4 = (p ^ 2) ^ 2 := by ring
        obtain ⟨v, hv⟩ : ∃ v, p ^ 2 = v + 1 := ⟨p ^ 2 - 1, by omega⟩
        rw [e, hv]
        simp only [Nat.add_sub_cancel]
        ring
      rw [sq]
      omega
    have hdu : d < p ^ 2 := by
      by_contra h
      push Not at h
      have hle := Nat.pow_le_pow_left h 2
      have e : (p ^ 2) ^ 2 = p ^ 4 := by ring
      rw [e] at hle
      omega
    have hud : p ^ 2 - 1 < d := by
      by_contra h
      push Not at h
      have hle := Nat.pow_le_pow_left h 2
      omega
    omega

/-- **Near $F_k$-perfect numbers.** For natural numbers $k$ and $n$, the number $n$ is near
$F_k$-perfect when it is $[k,3]$-near-perfect, that is, when some proper divisor $d$ of $n$
($d \mid n$ and $d < n$) satisfies $\sigma_k(n) = n^k + d^k + 3n$, where
$\sigma_k(n) = \sum_{e \mid n} e^k$ is the sum of the $k$-th powers of the divisors of $n$.

No condition $k > 1$ is imposed here; the results that need it assume it. -/
def IsNearFkPerfect (k n : ℕ) : Prop :=
  IsKLNearPerfect k 3 n

/-- **No near $F_k$-perfect number of the form $p_1^a p_2$.** Let $k > 1$, let $p_1$ and $p_2$ be
distinct odd primes and let $a$ be a natural number. Then $p_1^a p_2$ is not near $F_k$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 17. -/
theorem not_isNearFkPerfect_prime_pow_mul
    (k p₁ p₂ a : ℕ) (hk : 1 < k) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (ho₁ : Odd p₁) (ho₂ : Odd p₂)
    (hne : p₁ ≠ p₂) :
    ¬ IsNearFkPerfect k (p₁ ^ a * p₂) := by
  have _hk0 : k ≠ 0 := by omega
  rintro ⟨d, hd, hlt, hsum⟩
  have hn_odd : Odd (p₁ ^ a * p₂) := Odd.mul ho₁.pow ho₂
  have hd_odd : Odd d := by
    by_contra hcon
    rw [Nat.not_odd_iff_even] at hcon
    have h2d : 2 ∣ d := even_iff_two_dvd.mp hcon
    have h2n : 2 ∣ p₁ ^ a * p₂ := h2d.trans hd
    exact (Odd.not_two_dvd_nat hn_odd) h2n
  have hcop : Nat.Coprime (p₁ ^ a) p₂ :=
    Nat.Coprime.pow_left a ((Nat.coprime_primes hp₁ hp₂).mpr hne)
  have h1mem : (1 : ℕ) ∉ ({p₂} : Finset ℕ) := by
    simpa only [Finset.mem_singleton] using hp₂.ne_one.symm
  have hsig2 : ArithmeticFunction.sigma k p₂ = 1 + p₂ ^ k := by
    simp only [ArithmeticFunction.sigma_apply, hp₂.divisors, Finset.sum_insert h1mem,
      Finset.sum_singleton, one_pow]
  have hsig : (∑ e ∈ (p₁ ^ a * p₂).divisors, e ^ k) =
      (ArithmeticFunction.sigma k (p₁ ^ a)) * (1 + p₂ ^ k) := by
    rw [← ArithmeticFunction.sigma_apply,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsig2]
  have hbase_even : Even (1 + p₂ ^ k) := Odd.add_odd odd_one ho₂.pow
  have hLHS_even : Even (∑ e ∈ (p₁ ^ a * p₂).divisors, e ^ k) := by
    rw [hsig]
    exact Even.mul_left hbase_even _
  have hn_pow_odd : Odd ((p₁ ^ a * p₂) ^ k) := hn_odd.pow
  have hd_pow_odd : Odd (d ^ k) := hd_odd.pow
  have h3n_odd : Odd (3 * (p₁ ^ a * p₂)) :=
    Odd.mul (⟨1, rfl⟩ : Odd (3 : ℕ)) hn_odd
  have hRHS_odd : Odd ((p₁ ^ a * p₂) ^ k + d ^ k + 3 * (p₁ ^ a * p₂)) :=
    Even.add_odd (Odd.add_odd hn_pow_odd hd_pow_odd) h3n_odd
  rw [hsum] at hLHS_even
  exact (Nat.not_even_iff_odd.mpr hRHS_odd) hLHS_even

/-- **Deficient $F_k$-perfect numbers.** For natural numbers $k$ and $n$, write
$\sigma_k(n) = \sum_{e \mid n} e^k$. The number $n$ is deficient $F_k$-perfect when it is
$[k,3]$-deficient-perfect, that is, when there is a divisor $d$ of $n$ with $d < n$ such that
$\sigma_k(n) + d^k = n^k + 3n$.

This predicate extends the equation to every natural $k$. For $k > 1$ it agrees with
Definition 2 of Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia, "On Near
`F_k`-Perfect and Deficient `F_k`-Perfect Numbers", which uses the name only for $k > 1$; the
results that need $k > 1$ assume it. -/
def IsDeficientFkPerfect (k n : ℕ) : Prop :=
  IsKLDeficientPerfect k 3 n

private theorem odd_prod_of_odd (s : Finset ℕ) (hs : ∀ p ∈ s, Odd p) :
    Odd (∏ p ∈ s, p) := by
  revert hs
  induction s using Finset.induction_on with
  | empty =>
      intro hs
      simp
  | insert q qs hq ih =>
      intro hs
      rw [Finset.prod_insert hq]
      exact (hs q (Finset.mem_insert_self q qs)).mul
        (ih (fun p hp => hs p (Finset.mem_insert_of_mem hp)))

private theorem sigma_prod_eq (k : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∑ e ∈ (∏ p ∈ s, p).divisors, e ^ k = ∏ p ∈ s, (1 + p ^ k) := by
  revert hs
  induction s using Finset.induction_on with
  | empty =>
      intro hs
      simp only [Finset.prod_empty, Nat.divisors_one, Finset.sum_singleton, one_pow]
  | insert q qs hq ih =>
      intro hs
      have hs' : ∀ p ∈ qs, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have hq' : q.Prime := hs q (Finset.mem_insert_self q qs)
      have hcop : Nat.Coprime q (∏ p ∈ qs, p) := by
        apply Nat.Coprime.prod_right
        intro p hp
        exact (Nat.coprime_primes hq' (hs' p hp)).mpr (fun heq => hq (heq ▸ hp))
      have hprime : ∑ e ∈ q.divisors, e ^ k = 1 + q ^ k := by
        have h1 : (1 : ℕ) ∉ ({q} : Finset ℕ) := by
          simpa only [Finset.mem_singleton] using hq'.ne_one.symm
        simp only [hq'.divisors, Finset.sum_insert h1, Finset.sum_singleton, one_pow]
      rw [Finset.prod_insert hq, ← ArithmeticFunction.sigma_apply,
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply,
        hprime, ih hs', Finset.prod_insert hq]

/-- **No product of distinct odd primes is deficient $F_k$-perfect.** Let $k > 1$ and let $s$ be a
finite set of odd primes. Then $\prod_{p \in s} p$ is not deficient $F_k$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 21. -/
theorem not_isDeficientFkPerfect_prod_primes
    (k : ℕ) (hk : 1 < k) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ Odd p) :
    ¬ IsDeficientFkPerfect k (∏ p ∈ s, p) := by
  rintro ⟨d, hdvd, hlt, hsum⟩
  have _ : k ≠ 0 := by omega
  have hn : Odd (∏ p ∈ s, p) :=
    odd_prod_of_odd s (fun p hp => (hs p hp).2)
  rcases s.eq_empty_or_nonempty with rfl | ⟨q, hq⟩
  · simp only [Finset.prod_empty] at hdvd hlt
    exact (Nat.ne_of_lt hlt) (Nat.dvd_one.mp hdvd)
  · have hσ : Even (∑ e ∈ (∏ p ∈ s, p).divisors, e ^ k) := by
      rw [sigma_prod_eq k s (fun p hp => (hs p hp).1)]
      have hqeven : Even (1 + q ^ k) := ((hs q hq).2.pow).one_add
      rw [← Finset.mul_prod_erase s (fun p => 1 + p ^ k) hq]
      exact hqeven.mul_right _
    have hd : Odd d := by
      rcases Nat.even_or_odd d with hev | hod
      · exfalso
        have h2n : Even (∏ p ∈ s, p) :=
          even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hev).trans hdvd)
        have h0 : (∏ p ∈ s, p) % 2 = 0 := Nat.even_iff.mp h2n
        have h1 : (∏ p ∈ s, p) % 2 = 1 := Nat.odd_iff.mp hn
        omega
      · exact hod
    have hσ0 : (∑ e ∈ (∏ p ∈ s, p).divisors, e ^ k) % 2 = 0 := Nat.even_iff.mp hσ
    have hd1 : d ^ k % 2 = 1 := Nat.odd_iff.mp hd.pow
    have hn1 : (∏ p ∈ s, p) ^ k % 2 = 1 := Nat.odd_iff.mp hn.pow
    have h31 : (3 * ∏ p ∈ s, p) % 2 = 1 :=
      Nat.odd_iff.mp ((by decide : Odd 3).mul hn)
    omega

/-- **No deficient $F_k$-perfect number $p_1^a p_2^b$ with $a + b$ odd or $a, b$ both odd.** Let
$k > 1$ be a natural number, let $p_1 \ne p_2$ be odd primes and let $a, b \ge 1$ be natural
numbers such that $a + b$ is odd or both $a$ and $b$ are odd. Then $n = p_1^a p_2^b$ is not
deficient $F_k$-perfect: there is no divisor $d$ of $n$ with $d < n$ and
$\sigma_k(n) + d^k = n^k + 3n$, where $\sigma_k(n) = \sum_{e \mid n} e^k$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 19. -/
theorem not_isDeficientFkPerfect_pow_mul_pow
    (k p₁ p₂ a b : ℕ) (hk : 1 < k) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (ho₁ : Odd p₁) (ho₂ : Odd p₂)
    (hne : p₁ ≠ p₂) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hpar : Odd (a + b) ∨ (Odd a ∧ Odd b)) :
    ¬ IsDeficientFkPerfect k (p₁ ^ a * p₂ ^ b) := by
  -- `hk`, `ha` and `hb` are part of the stated result; the parity argument needs none of them.
  have _hk : 1 < k := hk
  have _ha : 1 ≤ a := ha
  have _hb : 1 ≤ b := hb
  rintro ⟨d, hdvd, _, hsum⟩
  have hn_odd : Odd (p₁ ^ a * p₂ ^ b) := ho₁.pow.mul ho₂.pow
  have hodd_of_dvd : ∀ e : ℕ, e ∣ p₁ ^ a * p₂ ^ b → Odd e := by
    intro e he
    by_contra hcon
    rw [Nat.not_odd_iff_even] at hcon
    exact (Nat.not_even_iff_odd.mpr hn_odd) (hcon.trans_dvd he)
  have hcop : Nat.Coprime (p₁ ^ a) (p₂ ^ b) :=
    Nat.coprime_pow_primes a b hp₁ hp₂ hne
  have hsig : ArithmeticFunction.sigma 0 (p₁ ^ a * p₂ ^ b)
      = ArithmeticFunction.sigma 0 (p₁ ^ a) * ArithmeticFunction.sigma 0 (p₂ ^ b) :=
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  have hcard : (p₁ ^ a * p₂ ^ b).divisors.card = (a + 1) * (b + 1) := by
    rw [ArithmeticFunction.sigma_zero_apply,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp₁,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp₂] at hsig
    exact hsig
  have hpar2 : Even (a + 1) ∨ Even (b + 1) := by
    rcases hpar with hodd | ⟨ha', _⟩
    · rcases Nat.even_or_odd a with hae | hao
      · have hb : Odd b := by
          rw [Nat.odd_iff]
          have hae' := Nat.even_iff.mp hae
          have hodd' := Nat.odd_iff.mp hodd
          omega
        exact Or.inr hb.add_one
      · exact Or.inl hao.add_one
    · exact Or.inl ha'.add_one
  have hcard_even : Even ((p₁ ^ a * p₂ ^ b).divisors.card) := by
    rw [hcard]
    exact hpar2.elim (fun h => h.mul_right _) (fun h => h.mul_left _)
  have hterm : ∀ e ∈ (p₁ ^ a * p₂ ^ b).divisors, e ^ k % 2 = 1 := by
    intro e he
    exact Nat.odd_iff.mp ((hodd_of_dvd e (Nat.dvd_of_mem_divisors he)).pow)
  have hsum0 : (∑ e ∈ (p₁ ^ a * p₂ ^ b).divisors, e ^ k) % 2 = 0 := by
    have hcongr : (∑ e ∈ (p₁ ^ a * p₂ ^ b).divisors, e ^ k % 2)
        = ∑ _e ∈ (p₁ ^ a * p₂ ^ b).divisors, 1 :=
      Finset.sum_congr rfl (fun e he => hterm e he)
    have h1 : (∑ e ∈ (p₁ ^ a * p₂ ^ b).divisors, e ^ k % 2)
        = (p₁ ^ a * p₂ ^ b).divisors.card := by
      rw [hcongr]
      simp
    rw [Finset.sum_nat_mod, h1]
    exact Nat.even_iff.mp hcard_even
  have hd1 : d ^ k % 2 = 1 := Nat.odd_iff.mp ((hodd_of_dvd d hdvd).pow)
  have hn1 : (p₁ ^ a * p₂ ^ b) ^ k % 2 = 1 := Nat.odd_iff.mp hn_odd.pow
  have h31 : 3 * (p₁ ^ a * p₂ ^ b) % 2 = 1 :=
    Nat.odd_iff.mp ((by decide : Odd 3).mul hn_odd)
  omega

private theorem odd_of_dvd_of_odd (e n : ℕ) (hn : Odd n) (he : e ∣ n) : Odd e := by
  by_contra hcon
  have hcon' : Even e := Nat.not_odd_iff_even.mp hcon
  have hneven : Even n := even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hcon').trans he)
  exact (Nat.not_even_iff_odd.mpr hn) hneven

private theorem card_divisors_prime_pow_mul_prime (p₁ p₂ a : ℕ) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂) :
    (p₁ ^ a * p₂).divisors.card = (a + 1) * 2 := by
  have hcop : (p₁ ^ a).Coprime p₂ :=
    Nat.Coprime.pow_left a ((Nat.coprime_primes hp₁ hp₂).mpr hne)
  have hσ := ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    (f := ArithmeticFunction.sigma 0) hcop
  simp only [ArithmeticFunction.sigma_zero_apply] at hσ
  have hpa : (p₁ ^ a).divisors.card = a + 1 := by
    rw [Nat.divisors_prime_pow hp₁ a, Finset.card_map, Finset.card_range]
  have hp2 : p₂.divisors.card = 2 := by
    rw [hp₂.divisors, Finset.card_insert_of_notMem (by
      simpa only [Finset.mem_singleton] using hp₂.ne_one.symm), Finset.card_singleton]
  rw [hσ, hpa, hp2]

private theorem even_sum_pow_of_forall_odd (s : Finset ℕ) (k : ℕ)
    (hodd : ∀ e ∈ s, Odd e) (hcard : Even s.card) :
    Even (∑ e ∈ s, e ^ k) := by
  rw [Nat.even_iff, Finset.sum_nat_mod]
  have h1 : ∀ e ∈ s, e ^ k % 2 = 1 := fun e he => Nat.odd_iff.mp ((hodd e he).pow)
  have hsum1 : (∑ e ∈ s, e ^ k % 2) = ∑ _e ∈ s, 1 :=
    Finset.sum_congr rfl (fun e he => h1 e he)
  obtain ⟨c, hc⟩ := hcard
  rw [hsum1, ← Finset.card_eq_sum_ones, hc]
  omega

/-- **No deficient $F_k$-perfect number $p_1^a p_2$ with distinct odd primes.** Let $k > 1$ be
a natural number, let $p_1 \ne p_2$ be odd primes and let $a$ be a natural number. Then
$p_1^a p_2$ is not deficient $F_k$-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 16. -/
theorem not_isDeficientFkPerfect_prime_pow_mul
    (k p₁ p₂ a : ℕ) (hk : 1 < k) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (ho₁ : Odd p₁) (ho₂ : Odd p₂)
    (hne : p₁ ≠ p₂) :
    ¬ IsDeficientFkPerfect k (p₁ ^ a * p₂) := by
  have _ : k ≠ 0 := by omega
  rintro ⟨d, hdvd, _hlt, hsum⟩
  have hn : Odd (p₁ ^ a * p₂) := ho₁.pow.mul ho₂
  have hcard : (p₁ ^ a * p₂).divisors.card = (a + 1) * 2 :=
    card_divisors_prime_pow_mul_prime p₁ p₂ a hp₁ hp₂ hne
  have hcardeven : Even (p₁ ^ a * p₂).divisors.card := ⟨a + 1, by rw [hcard]; ring⟩
  have hσeven : Even (∑ e ∈ (p₁ ^ a * p₂).divisors, e ^ k) :=
    even_sum_pow_of_forall_odd _ k
      (fun e he => odd_of_dvd_of_odd e _ hn (Nat.dvd_of_mem_divisors he)) hcardeven
  have hdk : Odd (d ^ k) := (odd_of_dvd_of_odd d _ hn hdvd).pow
  have hnk : Odd ((p₁ ^ a * p₂) ^ k) := hn.pow
  have h3 : Odd 3 := ⟨1, rfl⟩
  have h3n : Odd (3 * (p₁ ^ a * p₂)) := h3.mul hn
  obtain ⟨s, hs⟩ := hσeven
  obtain ⟨t, ht⟩ := hdk
  obtain ⟨u, hu⟩ := hnk
  obtain ⟨v, hv⟩ := h3n
  omega

private theorem sigma_prime_pow_eq (p a k : ℕ) (hp : p.Prime) :
    (∑ e ∈ (p ^ a).divisors, e ^ k) = ∑ j ∈ Finset.range (a + 1), p ^ (j * k) := by
  rw [← ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply_prime_pow hp]

private theorem geom_sum_modEq_one (p m k : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ∑ i ∈ Finset.range m, p ^ (i * k) ≡ 1 [MOD p] := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [show (1 : ℕ) + m' = m' + 1 from add_comm _ _]
  rw [Finset.sum_range_succ']
  have htail : p ∣ ∑ i ∈ Finset.range m', p ^ ((i + 1) * k) := by
    apply Finset.dvd_sum
    intro i _
    exact dvd_pow_self p (mul_ne_zero (by omega) (by omega))
  have h0 : p ^ (0 * k) = 1 := by simp
  rw [h0]
  simpa only [zero_add] using
    (Nat.modEq_zero_iff_dvd.mpr htail).add (Nat.ModEq.refl 1)

/-- **Prime powers that are $[k,\ell]$-near-perfect.** Let $p$ be a prime, let $a$, $k$, $\ell$
and $d$ be natural numbers with $k \ge 1$ and $\ell \ge 1$, and write
$\sigma_k(m) = \sum_{e \mid m} e^k$. Then $d$ is a proper divisor of $p^a$ ($d \mid p^a$ and
$d < p^a$) with $\sigma_k(p^a) = (p^a)^k + d^k + \ell p^a$ if and only if $2 \le a \le k$,
$d = 1$ and $\ell = p^{k-a} \sum_{i=0}^{a-2} p^{ik}$.

The source prints the conclusion $a = k$, which is false: for $p = 2$, $a = 2$, $k = 3$,
$\ell = 2$, $d = 1$ one has $\sigma_3(4) = 73 = 4^3 + 1^3 + 2 \cdot 4$ with $a \ne k$. The
printed form is the case $a = k$ of the identity $\sum_{i=1}^{a-1} p^{ik} = \ell p^a$.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 4. -/
theorem klNearPerfectWith_prime_pow_iff
    (p a k l d : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    KLNearPerfectWith k l (p ^ a) d ↔
      2 ≤ a ∧ a ≤ k ∧ d = 1 ∧
        l = p ^ (k - a) *
          ∑ i ∈ Finset.range (a - 1), p ^ (i * k) := by
  constructor
  · rintro ⟨hdvd, hlt, hsum⟩
    rw [sigma_prime_pow_eq p a k hp] at hsum
    obtain ⟨j, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hja' : j < a := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
    have e1 : (p ^ a) ^ k = p ^ (a * k) := by rw [← pow_mul]
    have e2 : (p ^ j) ^ k = p ^ (j * k) := by rw [← pow_mul]
    rw [Finset.sum_range_succ, e1, e2] at hsum
    have hmain : (∑ i ∈ Finset.range a, p ^ (i * k)) = p ^ (j * k) + l * p ^ a := by
      omega
    rcases eq_zero_or_pos j with rfl | hj
    · simp only [Nat.zero_mul, pow_zero] at hmain
      have ha1 : 1 ≤ a := by omega
      obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha1
      rw [show (1 : ℕ) + a' = a' + 1 from add_comm _ _] at hmain ⊢
      rw [Finset.sum_range_succ'] at hmain
      simp only [Nat.zero_mul, pow_zero] at hmain
      have htail : (∑ i ∈ Finset.range a', p ^ ((i + 1) * k)) = l * p ^ (a' + 1) := by
        omega
      have hfactor : (∑ i ∈ Finset.range a', p ^ ((i + 1) * k))
          = p ^ k * ∑ i ∈ Finset.range a', p ^ (i * k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [show (i + 1) * k = k + i * k by ring, pow_add]
      rw [hfactor] at htail
      have ha2 : 2 ≤ a' + 1 := by
        rcases eq_zero_or_pos a' with rfl | h
        · simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add] at htail
          have hpos : 0 < l * p ^ 1 := Nat.mul_pos hl (pow_pos hp.pos 1)
          omega
        · omega
      have hak : a' + 1 ≤ k := by
        by_contra hcon
        have hle : k ≤ a' + 1 := by omega
        have hsplit : p ^ (a' + 1) = p ^ k * p ^ (a' + 1 - k) := by
          conv_lhs => rw [← Nat.add_sub_cancel' hle]
          rw [pow_add]
        rw [hsplit] at htail
        have hcancel : (∑ i ∈ Finset.range a', p ^ (i * k)) = l * p ^ (a' + 1 - k) := by
          apply mul_left_cancel₀ (pow_ne_zero k hp.ne_zero)
          rw [htail]
          ring
        have hmod1 := geom_sum_modEq_one p a' k hk (by omega : 1 ≤ a')
        rw [hcancel] at hmod1
        have hmod0 : l * p ^ (a' + 1 - k) ≡ 0 [MOD p] :=
          Nat.modEq_zero_iff_dvd.mpr ((dvd_pow_self p (by omega)).trans (dvd_mul_left _ _))
        have h10 : (1 : ℕ) ≡ 0 [MOD p] := hmod1.symm.trans hmod0
        exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp h10)
      have hsplit2 : p ^ k = p ^ (a' + 1) * p ^ (k - (a' + 1)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hsplit2] at htail
      have hl_eq : l = p ^ (k - (a' + 1)) * ∑ i ∈ Finset.range a', p ^ (i * k) := by
        have h0 : p ^ (a' + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
        have h2 : l * p ^ (a' + 1)
            = (p ^ (k - (a' + 1)) * ∑ i ∈ Finset.range a', p ^ (i * k)) * p ^ (a' + 1) := by
          rw [← htail]
          ring
        exact mul_right_cancel₀ h0 h2
      refine ⟨ha2, hak, pow_zero p, ?_⟩
      rw [Nat.add_sub_cancel a' 1]
      exact hl_eq
    · have ha1 : 1 ≤ a := by omega
      have hmodL := geom_sum_modEq_one p a k hk ha1
      rw [hmain] at hmodL
      have hmod0 : p ^ (j * k) + l * p ^ a ≡ 0 [MOD p] := by
        have hd1 : p ∣ p ^ (j * k) := dvd_pow_self p (mul_ne_zero (by omega) (by omega))
        have hd2 : p ∣ l * p ^ a := (dvd_pow_self p (by omega)).trans (dvd_mul_left _ _)
        simpa only [add_zero] using
          (Nat.modEq_zero_iff_dvd.mpr hd1).add (Nat.modEq_zero_iff_dvd.mpr hd2)
      have h10 : (1 : ℕ) ≡ 0 [MOD p] := hmodL.symm.trans hmod0
      exact absurd (Nat.modEq_zero_iff_dvd.mp h10) hp.not_dvd_one
  · rintro ⟨ha2, hak, rfl, rfl⟩
    have ha1 : 1 ≤ a := by omega
    obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha1
    rw [show (1 : ℕ) + a' = a' + 1 from add_comm _ _]
    have hS : a' + 1 - 1 = a' := Nat.add_sub_cancel a' 1
    refine ⟨one_dvd _, ?_, ?_⟩
    · calc (1 : ℕ) < p := hp.one_lt
        _ ≤ p ^ (a' + 1) := Nat.le_self_pow (by omega) p
    · rw [hS, sigma_prime_pow_eq p (a' + 1) k hp, Finset.sum_range_succ]
      have e1 : (p ^ (a' + 1)) ^ k = p ^ ((a' + 1) * k) := by rw [← pow_mul]
      rw [e1, one_pow]
      have hmain : (∑ j ∈ Finset.range (a' + 1), p ^ (j * k))
          = 1 + (p ^ (k - (a' + 1)) * ∑ i ∈ Finset.range a', p ^ (i * k)) * p ^ (a' + 1) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.zero_mul, pow_zero]
        have htail : (∑ i ∈ Finset.range a', p ^ ((i + 1) * k))
            = p ^ k * ∑ i ∈ Finset.range a', p ^ (i * k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [show (i + 1) * k = k + i * k by ring, pow_add]
        have hL : (p ^ (k - (a' + 1)) * ∑ i ∈ Finset.range a', p ^ (i * k)) * p ^ (a' + 1)
            = p ^ k * ∑ i ∈ Finset.range a', p ^ (i * k) := by
          have hkk : p ^ (k - (a' + 1)) * p ^ (a' + 1) = p ^ k := by
            rw [← pow_add]
            congr 1
            omega
          calc (p ^ (k - (a' + 1)) * ∑ i ∈ Finset.range a', p ^ (i * k)) * p ^ (a' + 1)
              = (p ^ (k - (a' + 1)) * p ^ (a' + 1)) * ∑ i ∈ Finset.range a', p ^ (i * k) := by
                ring
            _ = p ^ k * ∑ i ∈ Finset.range a', p ^ (i * k) := by rw [hkk]
        rw [htail, hL]
        omega
      omega

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
