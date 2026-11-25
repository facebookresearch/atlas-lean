/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

/-!
# Proth's primality theorem

This file proves Proth's characterization of prime Proth numbers by a quadratic
nonresidue witness in `ZMod N`.
-/

namespace MetaMathlibExt

@[expose] public section

private theorem proth_arithmetic (h k N : ℕ) (hOdd : Odd h) (hlt : h < 2 ^ k)
    (hN : N = h * 2 ^ k + 1) :
    0 < h ∧ 0 < k ∧ 3 ≤ N ∧ Odd N ∧
      (N - 1) / 2 = h * 2 ^ (k - 1) ∧ (N - 1) / 2 = N / 2 := by
  have hh : 0 < h := hOdd.pos
  have hk : 0 < k := by
    by_contra hk
    have : k = 0 := by omega
    subst k
    simp only [pow_zero] at hlt
    omega
  have hrepr : N = 2 * (h * 2 ^ (k - 1)) + 1 := by
    calc
      N = h * 2 ^ k + 1 := hN
      _ = 2 * (h * 2 ^ (k - 1)) + 1 := by
        rw [← Nat.two_pow_pred_mul_two hk]
        ring
  have ht : 0 < h * 2 ^ (k - 1) := Nat.mul_pos hh (Nat.pow_pos (by omega))
  have hNodd : Odd N := by
    rw [hrepr]
    exact (even_two_mul _).add_one
  refine ⟨hh, hk, by omega, hNodd, ?_, ?_⟩ <;> omega

private theorem proth_prime_witness (N : ℕ) (hPrime : Nat.Prime N) (hNtwo : N ≠ 2) :
    ∃ a : ZMod N, a ^ (N / 2) = -1 := by
  let _ : Fact (Nat.Prime N) := ⟨hPrime⟩
  have hChar : ringChar (ZMod N) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hNtwo
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hChar
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    exact ha IsSquare.zero
  refine ⟨a, ?_⟩
  rcases ZMod.pow_div_two_eq_neg_one_or_one N ha0 with hone | hneg
  · exact (ha ((ZMod.euler_criterion N ha0).2 hone)).elim
  · exact hneg

private theorem proth_orderOf_eq_two_pow {R : Type*} [Ring R] [Nontrivial R]
    (x : R) (k : ℕ) (hk : 0 < k) (hChar : ringChar R ≠ 2)
    (hhalf : x ^ (2 ^ (k - 1)) = -1) : orderOf x = 2 ^ k := by
  have hnot : ¬orderOf x ∣ 2 ^ (k - 1) := by
    rw [orderOf_dvd_iff_pow_eq_one]
    intro hone
    exact Ring.neg_one_ne_one_of_char_ne_two hChar (hhalf.symm.trans hone)
  have hfull : x ^ (2 ^ k) = 1 := by
    rw [← Nat.two_pow_pred_mul_two hk, pow_mul, hhalf]
    simp
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hfull
  have hk' : k - 1 + 1 = k := by omega
  have horder : orderOf x = 2 ^ (k - 1 + 1) :=
    Nat.eq_prime_pow_of_dvd_least_prime_pow Nat.prime_two hnot (by simpa only [hk'])
  simpa only [hk'] using horder

private theorem proth_two_pow_dvd_orderOf {R : Type*} [Ring R] [Nontrivial R]
    (b : R) (h k : ℕ) (hk : 0 < k) (hChar : ringChar R ≠ 2)
    (hhalf : b ^ (h * 2 ^ (k - 1)) = -1) : 2 ^ k ∣ orderOf b := by
  have hxhalf : (b ^ h) ^ (2 ^ (k - 1)) = -1 := by
    rw [← pow_mul]
    exact hhalf
  have horder := proth_orderOf_eq_two_pow (b ^ h) k hk hChar hxhalf
  rw [← horder]
  exact orderOf_pow_dvd h

private theorem proth_two_pow_dvd_prime_sub_one (h k N q : ℕ) (hh : 0 < h)
    (hk : 0 < k) (hNodd : Odd N) (hqPrime : Nat.Prime q) (hqN : q ∣ N)
    (a : ZMod N) (ha : a ^ (h * 2 ^ (k - 1)) = -1) : 2 ^ k ∣ q - 1 := by
  let _ : Fact (Nat.Prime q) := ⟨hqPrime⟩
  have hq2 : q ≠ 2 := by
    intro hq2
    subst q
    exact hNodd.not_two_dvd_nat hqN
  have hChar : ringChar (ZMod q) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hq2
  let b : ZMod q := ZMod.castHom hqN (ZMod q) a
  have hbhalf : b ^ (h * 2 ^ (k - 1)) = -1 := by
    simpa only [b, map_pow, map_neg, map_one] using
      congrArg (ZMod.castHom hqN (ZMod q)) ha
  have hexp : 0 < h * 2 ^ (k - 1) := Nat.mul_pos hh (Nat.pow_pos (by omega))
  have hb0 : b ≠ 0 := by
    intro hb0
    rw [hb0, zero_pow hexp.ne'] at hbhalf
    exact (neg_ne_zero.mpr one_ne_zero) hbhalf.symm
  exact (proth_two_pow_dvd_orderOf b h k hk hChar hbhalf).trans
    (ZMod.orderOf_dvd_card_sub_one hb0)

private theorem proth_prime_divisor_lower_bound (h k N q : ℕ) (hh : 0 < h)
    (hk : 0 < k) (hNodd : Odd N) (hqPrime : Nat.Prime q) (hqN : q ∣ N)
    (a : ZMod N) (ha : a ^ (h * 2 ^ (k - 1)) = -1) : 2 ^ k + 1 ≤ q := by
  have hdvd := proth_two_pow_dvd_prime_sub_one h k N q hh hk hNodd hqPrime hqN a ha
  have hqTwo := hqPrime.two_le
  have hqSub : 0 < q - 1 := by omega
  have hle := Nat.le_of_dvd hqSub hdvd
  omega

private theorem proth_composite_impossible (h k N : ℕ) (hh : 0 < h) (hk : 0 < k)
    (hNge : 3 ≤ N) (hNodd : Odd N) (hlt : h < 2 ^ k) (hN : N = h * 2 ^ k + 1)
    (a : ZMod N) (ha : a ^ (h * 2 ^ (k - 1)) = -1) (hComposite : ¬Nat.Prime N) : False := by
  let q := N.minFac
  have hqPrime : Nat.Prime q := Nat.minFac_prime (by omega)
  have hqN : q ∣ N := Nat.minFac_dvd N
  have hqLower :=
    proth_prime_divisor_lower_bound h k N q hh hk hNodd hqPrime hqN a ha
  have hqSq : q ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hComposite
  have hLowerSq : (2 ^ k + 1) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hqLower 2
  have hpowPos : 0 < 2 ^ k := Nat.pow_pos (by omega)
  have hmulLt : h * 2 ^ k < 2 ^ k * 2 ^ k :=
    (Nat.mul_lt_mul_right hpowPos).2 hlt
  have hNlt : N < (2 ^ k) ^ 2 + 1 := by
    rw [hN, pow_two]
    omega
  have hsqGap : (2 ^ k) ^ 2 + 1 < (2 ^ k + 1) ^ 2 := by
    nlinarith
  omega

/-- **Proth's theorem.** Let $h$ and $k$ be natural numbers with $h$ odd and $h < 2^k$, and let
$N = h \cdot 2^k + 1$. Then $N$ is prime if and only if there is a residue class $a$ modulo $N$
with $a^{(N-1)/2} = -1$ in $\mathbb{Z}/N\mathbb{Z}$.

Proof: The forward implication uses a nonsquare and Euler's criterion; the reverse uses Proth's
least-prime-factor order argument. Sources: Proth (1878), p. 926, and the Wikipedia exposition.

Proves `Wanted` entry `proth_theorem`.

Source: https://en.wikipedia.org/wiki/Proth%27s_theorem
-/
theorem proth_theorem (h k N : ℕ) (hOdd : Odd h) (hlt : h < 2 ^ k)
    (hN : N = h * 2 ^ k + 1) :
    Nat.Prime N ↔ ∃ a : ZMod N, a ^ ((N - 1) / 2) = -1 := by
  obtain ⟨hh, hk, hNge, hNodd, hexp, hhalf⟩ := proth_arithmetic h k N hOdd hlt hN
  constructor
  · intro hPrime
    obtain ⟨a, ha⟩ := proth_prime_witness N hPrime (by omega)
    refine ⟨a, ?_⟩
    rw [hhalf]
    exact ha
  · rintro ⟨a, ha⟩
    by_contra hComposite
    exact proth_composite_impossible h k N hh hk hNge hNodd hlt hN a (by
      rw [← hexp]
      exact ha) hComposite

end

end MetaMathlibExt
