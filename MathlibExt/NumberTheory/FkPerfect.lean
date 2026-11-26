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
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors

/-! # Near and deficient `F_k`-perfect numbers

Results from Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia,
"On Near `F_k`-Perfect and Deficient `F_k`-Perfect Numbers", *INTEGERS* 25 (2025),
Article A86 (<https://math.colgate.edu/~integers/z86/z86.pdf>).

## Main statements

* `klDeficientPerfectWith_one_prime_pow_iff`: the prime power `p ^ a` is
  `[1,ℓ]`-deficient-perfect with divisor `d` if and only if `p = 2`, `ℓ = 1`, `d = 1` and
  `a ≥ 1`. This is the `k = 1` part of Theorem 5.
* `not_isKLNearPerfect_two_mul_prime`: for `1 ≤ ℓ` and an odd prime `p`, `2 * p` is not
  `[k,ℓ]`-near-perfect (Theorem 6). The divisor sum factors as `(1 + 2 ^ k) * (1 + p ^ k)`, and
  for each proper divisor `1`, `2`, `p` the equation fails by parity or by divisibility by `p`.
* `not_isNearFPerfect_two_pow_mul_prime_pow`: for a prime `p` and even `b`, the number
  `2 ^ a * p ^ b` is not near `F`-perfect: no proper divisor `d` satisfies
  `σ₂(n) = n ^ 2 + d ^ 2 + 3 * n` (Theorem 15). Prime powers are excluded by reducing the
  divisor-sum equation modulo `p ^ 2`. For odd `p` with both exponents positive, the four
  divisors `1`, `n / 2`, `n / p` and `n` force `n < 3 * p ^ 2`, leaving only `n = 2 * p ^ 2`,
  which is excluded by squeezing `d` between consecutive squares.
* `not_isNearFkPerfect_prime_pow_mul`: for `k > 1` and distinct odd primes `p₁` and `p₂`, no
  number `p₁ ^ a * p₂` is near `F_k`-perfect (Theorem 17). Multiplicativity gives
  `σₖ(n) = σₖ(p₁ ^ a) * (1 + p₂ ^ k)`, which is even, while `n ^ k + d ^ k + 3 * n` is odd.
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

/-- **Twice an odd prime is not $[k,\ell]$-near-perfect.** Let $k$ and $\ell$ be natural numbers
with $\ell \ge 1$ and let $p$ be an odd prime. Then $2p$ is not $[k,\ell]$-near-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 6. -/
theorem not_isKLNearPerfect_two_mul_prime (k l p : ℕ)
    (hl : 1 ≤ l) (hp : p.Prime) (hpo : Odd p) :
    ¬ IsKLNearPerfect k l (2 * p) := by
  rintro ⟨d, hd, hlt, hsum⟩
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hpo
  have htwo : ArithmeticFunction.sigma k 2 = 1 + 2 ^ k := by
    simp [ArithmeticFunction.sigma_apply, Nat.prime_two.divisors]
  have h1 : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
    simpa only [Finset.mem_singleton] using hp.ne_one.symm
  have hpsig : ArithmeticFunction.sigma k p = 1 + p ^ k := by
    simp [ArithmeticFunction.sigma_apply, hp.divisors, Finset.sum_insert h1]
  have hsigma : (∑ e ∈ (2 * p).divisors, e ^ k) = (1 + 2 ^ k) * (1 + p ^ k) := by
    rw [← ArithmeticFunction.sigma_apply,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, htwo, hpsig]
  rw [hsigma] at hsum
  have hprod : (1 + 2 ^ k) * (1 + p ^ k) = 1 + 2 ^ k + p ^ k + (2 * p) ^ k := by
    rw [mul_pow]; ring
  rw [hprod] at hsum
  have hmain : 1 + 2 ^ k + p ^ k = d ^ k + l * (2 * p) := by
    have h2 : (2 * p) ^ k + d ^ k + l * (2 * p)
        = d ^ k + l * (2 * p) + (2 * p) ^ k := by ac_rfl
    rw [h2] at hsum
    exact Nat.add_right_cancel hsum
  have hdiv : d = 1 ∨ d = 2 ∨ d = p := by
    by_cases hpd : p ∣ d
    · obtain ⟨f, rfl⟩ := hpd
      rw [mul_comm 2 p] at hd
      have hd2 : f ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hp.pos hd
      rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with rfl | rfl
      · exact Or.inr (Or.inr (mul_one p))
      · exfalso
        rw [mul_comm p 2] at hlt
        exact lt_irrefl _ hlt
    · have hcop' : Nat.Coprime d p := (hp.coprime_iff_not_dvd.mpr hpd).symm
      have hd2 : d ∣ 2 := hcop'.dvd_of_dvd_mul_right hd
      rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp only [pow_zero] at hmain
    have hcon : l * (2 * p) = 2 := by omega
    have h := Nat.mul_le_mul_right (2 * p) hl
    rw [one_mul, hcon] at h
    have h2 := hp.two_le
    omega
  · have h2keven : Even (2 ^ k) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
    have heven : Even (l * (2 * p)) := ⟨l * p, by ring⟩
    rcases hdiv with rfl | rfl | hdp
    · simp only [one_pow] at hmain
      have hodd : Odd (p ^ k) := hpo.pow
      have hLHS : Even (1 + 2 ^ k + p ^ k) := (odd_one.add_even h2keven).add_odd hodd
      have hRHS : Odd (1 + l * (2 * p)) := odd_one.add_even heven
      rw [hmain] at hLHS
      exact (Nat.not_odd_iff_even.mpr hLHS) hRHS
    · have h1pk : 1 + p ^ k = l * (2 * p) := by omega
      have hpd1 : p ∣ 1 := by
        have h1 : p ∣ p ^ k := dvd_pow_self p (by omega)
        have h2 : p ∣ l * (2 * p) := ⟨2 * l, by ring⟩
        rw [← h1pk] at h2
        exact (Nat.dvd_add_left h1).mp h2
      exact hp.not_dvd_one hpd1
    · rw [hdp] at hmain
      have h12k : 1 + 2 ^ k = l * (2 * p) := by omega
      have hLHS : Odd (1 + 2 ^ k) := odd_one.add_even h2keven
      rw [h12k] at hLHS
      exact (Nat.not_even_iff_odd.mpr hLHS) heven

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

end MathlibExt.NumberTheory.FkPerfectWanted
