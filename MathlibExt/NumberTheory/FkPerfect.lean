/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import MathlibExt.NumberTheory.OddPrimeDeficientPerfect
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors

/-!
# Near `F_k`-perfect and deficient `F_k`-perfect numbers

Results from Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia,
"On Near `F_k`-Perfect and Deficient `F_k`-Perfect Numbers".

## Main statements

* `klDeficientPerfectWith_one_prime_pow_iff`: the prime power `p ^ a` is
  `[1,ℓ]`-deficient-perfect with divisor `d` if and only if `p = 2`, `ℓ = 1`, `d = 1` and
  `a ≥ 1`. This is the `k = 1` part of Theorem 5.
* `not_isDeficientFkPerfect_prod_primes`: for `k > 1` and a finite set `s` of odd primes,
  `∏ p ∈ s, p` is not deficient `F_k`-perfect. This is Theorem 21.
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

/-- **Deficient $F_k$-perfect numbers.** For natural numbers $k$ and $n$, write
$\sigma_k(n) = \sum_{e \mid n} e^k$. The number $n$ is deficient $F_k$-perfect when it is
$[k,3]$-deficient-perfect, that is, when there is a divisor $d$ of $n$ with $d < n$ such that
$\sigma_k(n) + d^k = n^k + 3n$. -/
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

end MathlibExt.NumberTheory.FkPerfectWanted
