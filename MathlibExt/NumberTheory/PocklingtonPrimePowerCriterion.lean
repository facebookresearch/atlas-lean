/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Linarith

/-!
# Pocklington's prime-power criterion

This file proves Pocklington's primality criterion for numbers of the form
`N = K * p ^ e + 1`, using an order argument modulo a least prime factor of `N`.
-/

@[expose] public section

namespace MetaMathlibExt

private theorem pocklington_exponent_arithmetic (N K p e : ℕ)
    (hKpos : 0 < K) (hp : Nat.Prime p)
    (hN : N = K * p ^ e + 1) (hlt : K < p ^ e) :
    0 < e ∧ 2 ≤ N ∧ N - 1 = K * p ^ e ∧
      (N - 1) / p = K * p ^ (e - 1) := by
  have he : 0 < e := by
    by_contra he
    have : e = 0 := Nat.eq_zero_of_not_pos he
    subst e
    simp only [pow_zero] at hlt
    omega
  have hpowpos : 0 < p ^ e := Nat.pow_pos hp.pos
  have hNge : 2 ≤ N := by
    rw [hN]
    have : 0 < K * p ^ e := Nat.mul_pos hKpos hpowpos
    omega
  have hNm1 : N - 1 = K * p ^ e := by omega
  refine ⟨he, hNge, hNm1, ?_⟩
  rw [hNm1, show e = e - 1 + 1 by omega, pow_succ, ← mul_assoc]
  exact Nat.mul_div_cancel _ hp.pos

private theorem pocklington_reduced_power_ne_one (N p a q : ℕ)
    (hqPrime : Nat.Prime q) (hqN : q ∣ N)
    (hgcd : Nat.gcd (a ^ ((N - 1) / p) - 1) N = 1) :
    (a : ZMod q) ^ ((N - 1) / p) ≠ 1 := by
  intro hpow
  have hcast : (↑(a ^ ((N - 1) / p)) : ZMod q) = (1 : ℕ) := by
    simpa only [Nat.cast_pow, Nat.cast_one] using hpow
  have hmod : Nat.ModEq q (a ^ ((N - 1) / p)) 1 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have hqSub : q ∣ a ^ ((N - 1) / p) - 1 := hmod.symm.dvd'
  have hqGcd : q ∣ Nat.gcd (a ^ ((N - 1) / p) - 1) N := Nat.dvd_gcd hqSub hqN
  rw [hgcd] at hqGcd
  exact hqPrime.ne_one (Nat.dvd_one.mp hqGcd)

private theorem pocklington_prime_power_dvd_sub_one (N K p e a q : ℕ)
    (hp : Nat.Prime p) (he : 0 < e)
    (hqPrime : Nat.Prime q) (hqN : q ∣ N)
    (hNm1 : N - 1 = K * p ^ e)
    (hdiv : (N - 1) / p = K * p ^ (e - 1))
    (hmod : Nat.ModEq N (a ^ (N - 1)) 1)
    (hgcd : Nat.gcd (a ^ ((N - 1) / p) - 1) N = 1) :
    p ^ e ∣ q - 1 := by
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  let _ : Fact (Nat.Prime q) := ⟨hqPrime⟩
  have hfullA : (a : ZMod q) ^ (N - 1) = 1 := by
    have hcast : (↑(a ^ (N - 1)) : ZMod q) = (1 : ℕ) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.of_dvd hqN hmod)
    simpa only [Nat.cast_pow, Nat.cast_one] using hcast
  have hnotA : (a : ZMod q) ^ ((N - 1) / p) ≠ 1 :=
    pocklington_reduced_power_ne_one N p a q hqPrime hqN hgcd
  let y : ZMod q := (a : ZMod q) ^ K
  have hfullY : y ^ (p ^ e) = 1 := by
    change ((a : ZMod q) ^ K) ^ (p ^ e) = 1
    rw [← pow_mul, ← hNm1]
    exact hfullA
  have hnotY : y ^ (p ^ (e - 1)) ≠ 1 := by
    simpa only [hdiv, pow_mul, y] using hnotA
  have hpred : e - 1 + 1 = e := by omega
  have horder : orderOf y = p ^ e := by
    have horder' := orderOf_eq_prime_pow hnotY (by
      rw [hpred]
      exact hfullY)
    simpa only [hpred] using horder'
  have hy0 : y ≠ 0 := by
    intro hy0
    rw [hy0, zero_pow (Nat.pow_pos hp.pos).ne'] at hfullY
    exact zero_ne_one hfullY
  rw [← horder]
  exact ZMod.orderOf_dvd_card_sub_one hy0

private theorem pocklington_prime_divisor_lower_bound (N K p e a q : ℕ)
    (hp : Nat.Prime p) (he : 0 < e)
    (hqPrime : Nat.Prime q) (hqN : q ∣ N)
    (hNm1 : N - 1 = K * p ^ e)
    (hdiv : (N - 1) / p = K * p ^ (e - 1))
    (hmod : Nat.ModEq N (a ^ (N - 1)) 1)
    (hgcd : Nat.gcd (a ^ ((N - 1) / p) - 1) N = 1) :
    p ^ e + 1 ≤ q := by
  have hdvd := pocklington_prime_power_dvd_sub_one N K p e a q hp he hqPrime hqN
    hNm1 hdiv hmod hgcd
  have hqTwo := hqPrime.two_le
  have hqSub : 0 < q - 1 := by omega
  have hle := Nat.le_of_dvd hqSub hdvd
  omega

private theorem pocklington_factor_bound_contradiction (N K p e q : ℕ)
    (hp : Nat.Prime p) (hN : N = K * p ^ e + 1) (hlt : K < p ^ e)
    (hqLower : p ^ e + 1 ≤ q) (hqSq : q ^ 2 ≤ N) : False := by
  have hLowerSq : (p ^ e + 1) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hqLower 2
  have hpowPos : 0 < p ^ e := Nat.pow_pos hp.pos
  have hmulLt : K * p ^ e < p ^ e * p ^ e :=
    (Nat.mul_lt_mul_right hpowPos).2 hlt
  have hNlt : N < (p ^ e) ^ 2 + 1 := by
    rw [hN, pow_two]
    omega
  have hsqGap : (p ^ e) ^ 2 + 1 < (p ^ e + 1) ^ 2 := by
    nlinarith
  omega

/-- **Pocklington's criterion for $N = Kp^e + 1$.** Let $N$, $K$ and $e$ be natural numbers and
let $p$ be a prime, with $0 < K < p^e$ and $N = Kp^e + 1$. If some natural number $a$ satisfies
$a^{N-1} \equiv 1 \pmod{N}$ and $\gcd\big(a^{(N-1)/p} - 1, N\big) = 1$, where $(N-1)/p$ is the
quotient of $N - 1$ by $p$ rounded down and $a^{(N-1)/p} - 1$ is truncated at $0$, then $N$ is
prime.

Proof: The proof follows Pocklington's standard least-prime-factor order argument, from
Pocklington (1914) as stated by Grau and Oller-Marcen, arXiv:1011.4836v3, lines 60-69.

Proves `Wanted` entry `pocklington_prime_power_criterion`.

Source: Pocklington (1914), as stated in Grau and Oller-Marcen, "A primality test for Kp^n+1
numbers", arXiv:1011.4836v3, lines 60-69, which give the complete condition, including
gcd(a^((N-1)/p)-1,N)=1. The source's integer witness a ∈ ℤ is represented here by a natural
residue representative a : ℕ, using Nat.ModEq and Nat.gcd with natural subtraction in the
exponents.
-/
public theorem pocklington_prime_power_criterion (N K p e : ℕ)
    (hKpos : 0 < K) (hp : Nat.Prime p)
    (hN : N = K * p ^ e + 1) (hlt : K < p ^ e)
    (hex : ∃ a : ℕ, Nat.ModEq N (a ^ (N - 1)) 1 ∧
      Nat.gcd (a ^ ((N - 1) / p) - 1) N = 1) :
    Nat.Prime N := by
  obtain ⟨he, hNge, hNm1, hdiv⟩ :=
    pocklington_exponent_arithmetic N K p e hKpos hp hN hlt
  obtain ⟨a, hmod, hgcd⟩ := hex
  by_contra hComposite
  let q := N.minFac
  have hqPrime : Nat.Prime q := Nat.minFac_prime (by omega)
  have hqN : q ∣ N := Nat.minFac_dvd N
  have hqLower := pocklington_prime_divisor_lower_bound N K p e a q hp he hqPrime hqN
    hNm1 hdiv hmod hgcd
  have hqSq : q ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hComposite
  exact pocklington_factor_bound_contradiction N K p e q hp hN hlt hqLower hqSq

end MetaMathlibExt
