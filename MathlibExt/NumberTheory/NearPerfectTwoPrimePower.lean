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
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! # Near-perfect numbers of the form `2 * p ^ a`

Factoring the divisor sum and reducing modulo `2` determines the parity of the
omitted divisor. Reduction modulo `p` and `p ^ 2` gives the divisibility condition.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- **$[k,\ell]$-near-perfect with a given divisor.** For natural numbers $k$, $\ell$, $n$ and
$d$, the number $n$ is $[k,\ell]$-near-perfect with divisor $d$ when $d$ is a proper divisor of
$n$ ($d \mid n$ and $d < n$) and $\sigma_k(n) = n^k + d^k + \ell n$, where
$\sigma_k(n) = \sum_{e \mid n} e^k$ is the sum of the $k$-th powers of the divisors of $n$. -/
def KLNearPerfectWith (k l n d : ℕ) : Prop :=
  d ∣ n ∧ d < n ∧
    (∑ e ∈ n.divisors, e ^ k) = n ^ k + d ^ k + l * n

private theorem nearPerfect_rhs_modEq {m n d k l : ℕ} (hn : m ∣ n) (hk : k ≠ 0) :
    n ^ k + d ^ k + l * n ≡ d ^ k [MOD m] := by
  have hn0 := Nat.modEq_zero_iff_dvd.mpr hn
  simpa only [zero_pow hk, mul_zero, zero_add, add_zero] using
    ((hn0.pow k).add (Nat.ModEq.refl (d ^ k))).add (hn0.mul_left l)

/-- **A divisibility condition for near-perfect numbers $2p^a$.** Let $p$ be an odd prime, let
$a$, $k$, $\ell$ and $d$ be natural numbers with $k > 1$ and $\ell \ge 1$, and write
$\sigma_k(m) = \sum_{e \mid m} e^k$. If $d$ is a proper divisor of $2p^a$ ($d \mid 2p^a$ and
$d < 2p^a$) with $\sigma_k(2p^a) = (2p^a)^k + d^k + \ell \cdot 2p^a$, then $p^2 \mid 1 + 2^k$,
and $a$ is even if and only if $d$ is odd.

This is part 2 of Theorem 14 of the source.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 14. -/
theorem klNearPerfectWith_two_mul_prime_pow_imp
    (p a k l d : ℕ) (hp : p.Prime) (hpo : Odd p) (hk : 1 < k)
    (hl : 1 ≤ l) :
    KLNearPerfectWith k l (2 * p ^ a) d →
      p ^ 2 ∣ 1 + 2 ^ k ∧ (Even a ↔ Odd d) := by
  rintro ⟨hd, hlt, hsum⟩
  have hk0 : k ≠ 0 := by omega
  have hcop := Nat.coprime_two_left.mpr hpo
  have hsigma : (∑ e ∈ (2 * p ^ a).divisors, e ^ k) =
      (1 + 2 ^ k) * ∑ i ∈ Finset.range (a + 1), p ^ (i * k) := by
    have htwo : ArithmeticFunction.sigma k 2 = 1 + 2 ^ k := by
      simp [ArithmeticFunction.sigma_apply, Nat.prime_two.divisors]
    rw [← ArithmeticFunction.sigma_apply,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_right a),
      htwo, ArithmeticFunction.sigma_apply_prime_pow hp]
  rw [hsigma] at hsum
  -- Modulo two, every term of the prime-power sum contributes one.
  have hparity : Even a ↔ Odd d := by
    have hp1 : p ≡ 1 [MOD 2] := by simpa [Nat.ModEq] using Nat.odd_iff.mp hpo
    have hcount (b : ℕ) : (∑ i ∈ Finset.range b, p ^ (i * k)) ≡ b [MOD 2] := by
      induction b with
      | zero => simpa only [Finset.range_zero, Finset.sum_empty] using
          (Nat.ModEq.refl (n := 2) 0)
      | succ b ih =>
        rw [Finset.sum_range_succ]
        simpa only [one_pow, Nat.succ_eq_add_one] using ih.add (hp1.pow (b * k))
    have htwo : (2 : ℕ) ^ k ≡ 0 [MOD 2] := Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self 2 hk0)
    have hleft : (1 + 2 ^ k) * (∑ i ∈ Finset.range (a + 1), p ^ (i * k)) ≡ a + 1 [MOD 2] := by
      simpa only [add_zero, one_mul] using ((Nat.ModEq.refl 1).add htwo).mul (hcount (a + 1))
    rw [hsum] at hleft
    have hright : (2 * p ^ a) ^ k + d ^ k + l * (2 * p ^ a) ≡ d ^ k [MOD 2] :=
      nearPerfect_rhs_modEq (dvd_mul_right 2 (p ^ a)) hk0
    have hmod : d ^ k % 2 = (a + 1) % 2 := hright.symm.trans hleft
    rw [Nat.even_iff, ← Nat.odd_pow_iff hk0, Nat.odd_iff]
    omega
  have ha : a ≠ 0 := by
    intro ha
    subst a
    simp only [pow_zero, mul_one] at hd hlt
    have hd1 : d = 1 := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_right (Nat.ne_of_lt hlt)
    change (1 + 2 ^ k) * (∑ i ∈ Finset.range 1, p ^ (i * k)) = 2 ^ k + d ^ k + l * 2 at hsum
    simp only [Finset.sum_range_one, Nat.zero_mul, pow_zero, mul_one, hd1, one_pow] at hsum
    omega
  -- Only the constant term in the prime-power sum survives modulo `p ^ 2`.
  have htail : p ^ 2 ∣ ∑ i ∈ Finset.range a, p ^ ((i + 1) * k) := by
    apply Finset.dvd_sum
    intro i _
    exact Nat.pow_dvd_pow p ((show 2 ≤ k by omega).trans (Nat.le_mul_of_pos_left k (by omega)))
  have hgeom : (∑ i ∈ Finset.range (a + 1), p ^ (i * k)) ≡ 1 [MOD p ^ 2] := by
    rw [Finset.sum_range_succ', Nat.zero_mul, pow_zero]
    simpa only [zero_add] using (Nat.modEq_zero_iff_dvd.mpr htail).add (Nat.ModEq.refl 1)
  have hfund : (2 * p ^ a) ^ k + d ^ k + l * (2 * p ^ a) ≡ 1 + 2 ^ k [MOD p ^ 2] := by
    rw [← hsum]
    simpa only [mul_one] using hgeom.mul_left (1 + 2 ^ k)
  -- If `p` did not divide `d`, then `d` would divide two, contradicting the equation mod `p`.
  have hpd : p ∣ d := by
    by_contra hnd
    have hright : (2 * p ^ a) ^ k + d ^ k + l * (2 * p ^ a) ≡ d ^ k [MOD p] :=
      nearPerfect_rhs_modEq (dvd_mul_of_dvd_right (dvd_pow_self p ha) 2) hk0
    have hmod := (hfund.of_dvd (dvd_pow_self p (by decide : 2 ≠ 0))).symm.trans hright
    have hnp2 : ¬ p ∣ (2 : ℕ) ^ k :=
      fun h => (hp.coprime_iff_not_dvd.mp hcop.symm) (hp.dvd_of_dvd_pow h)
    rcases (Nat.dvd_prime Nat.prime_two).mp
        ((hp.coprime_pow_of_not_dvd hnd).dvd_of_dvd_mul_right hd) with rfl | rfl
    · rw [one_pow] at hmod
      have h2 : 2 ^ k ≡ 0 [MOD p] := (Nat.ModEq.refl 1).add_iff_left.mp (by simpa using hmod)
      exact hnp2 (Nat.modEq_zero_iff_dvd.mp h2)
    · have h1 : 1 ≡ 0 [MOD p] := (Nat.ModEq.refl (2 ^ k)).add_iff_right.mp (by simpa using hmod)
      exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp h1)
  -- For `a = 1`, parity would force `2 * p ∣ d`, contrary to properness.
  have ha2 : 2 ≤ a := by
    by_contra h
    have ha1 : a = 1 := by omega
    subst a
    have hde : Even d := Nat.not_odd_iff_even.mp fun hdo => (by decide : ¬ Even (1 : ℕ))
      (hparity.mpr hdo)
    have hdiv := hcop.mul_dvd_of_dvd_of_dvd (even_iff_two_dvd.mp hde) hpd
    rw [pow_one] at hd hlt
    exact (Nat.ne_of_lt hlt) (Nat.dvd_antisymm hd hdiv)
  have hright : (2 * p ^ a) ^ k + d ^ k + l * (2 * p ^ a) ≡ d ^ k [MOD p ^ 2] :=
    nearPerfect_rhs_modEq (dvd_mul_of_dvd_right (Nat.pow_dvd_pow p ha2) 2) hk0
  have hd0 : d ^ k ≡ 0 [MOD p ^ 2] :=
    Nat.modEq_zero_iff_dvd.mpr ((pow_dvd_pow_of_dvd hpd 2).trans (Nat.pow_dvd_pow d (by omega)))
  exact ⟨Nat.modEq_zero_iff_dvd.mp (hfund.symm.trans (hright.trans hd0)), hparity⟩

end MathlibExt.NumberTheory.FkPerfectWanted
