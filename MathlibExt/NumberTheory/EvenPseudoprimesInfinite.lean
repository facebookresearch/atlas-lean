/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Finite.Defs
public import MathlibExt.NumberTheory.EvenPseudoprime
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Order.Preorder.Finite
import MathlibExt.NumberTheory.BangZsigmondy

/-!
# Beeger's theorem

The set of even pseudoprimes is infinite. Starting with Lehmer's example `161038`, we enlarge
an even pseudoprime `N` by adjoining a primitive prime divisor of `2 ^ (N - 1) - 1`.
-/

namespace MathlibExt.NumberTheory.EvenPseudoprimesWanted

open MetaMathlibExt

/-- At an odd index `n > 1`, a primitive prime factor `p` of `2 ^ n - 1` satisfies `n ∣ p - 1`. -/
private theorem exists_prime_of_order {n : ℕ} (hn : 1 < n) (hodd : Odd n) :
    ∃ p : ℕ, p.Prime ∧ n ∣ p - 1 ∧ 2 ^ n ≡ 1 [MOD p] := by
  have hexc : ¬ IsBangZsigmondyExceptional 2 1 n := by
    obtain ⟨k, hk⟩ := hodd
    rintro (⟨_, _, h⟩ | ⟨h, _⟩) <;> omega
  obtain ⟨p, hp⟩ := bangZsigmondy_exists_primitivePrimeDivisor (by decide : 0 < 1)
    (by decide : 1 < 2) (by decide) hn hexc
  have : Fact p.Prime := ⟨hp.prime⟩
  have hdvd (m : ℕ) : (p : ℤ) ∣ (2 : ℤ) ^ m - 1 ^ m ↔ (2 : ZMod p) ^ m = 1 := by
    simp [← ZMod.intCast_zmod_eq_zero_iff_dvd, sub_eq_zero]
  have hpow := (hdvd n).mp hp.dvd
  have hord : orderOf (2 : ZMod p) = n :=
    (orderOf_eq_iff (by omega)).mpr
      ⟨hpow, fun m hlt hm h => hp.not_dvd_of_lt hm hlt ((hdvd m).mpr h)⟩
  have hne : (2 : ZMod p) ≠ 0 := by
    intro h
    simp [h, zero_pow (by omega : n ≠ 0)] at hpow
  refine ⟨p, hp.prime, hord ▸ ZMod.orderOf_dvd_card_sub_one hne, ?_⟩
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  simpa using hpow

/-- A congruence at exponent `n + 1` repeats at every exponent `n * k + 1`. -/
private theorem pow_mul_add_one_modEq {a n m : ℕ} (h : a ^ (n + 1) ≡ a [MOD m]) (k : ℕ) :
    a ^ (n * k + 1) ≡ a [MOD m] := by
  induction k with
  | zero => simp [Nat.ModEq]
  | succ k ih =>
    rw [Nat.mul_succ, add_right_comm, pow_add]
    exact (ih.mul_right (a ^ n)).trans (by simpa [pow_succ'] using h)

private theorem exists_larger {N : ℕ} (hN : IsEvenPseudoprime N) :
    ∃ M ∈ evenPseudoprimes, N < M := by
  have htwo := hN.two_lt
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hodd : Odd n := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hN.even)
  obtain ⟨p, hp, hdiv, hpow⟩ := exists_prime_of_order (by omega : 1 < n) hodd
  have hp₁ := hp.one_lt
  have hle := Nat.le_of_dvd (by omega : 0 < p - 1) hdiv
  have hlt : n + 1 < p := by
    have hne : n + 1 ≠ p := by
      rintro rfl
      exact hN.not_prime hp
    omega
  have hcop := (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hlt)).symm
  -- The same exponent works modulo both coprime factors.
  have hperiod : 2 ^ (n + 1) ≡ 2 [MOD (n + 1) * p] := by
    apply (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
    exact ⟨hN.modeq, by simpa [pow_succ] using hpow.mul_right 2⟩
  obtain ⟨k, hk⟩ := hdiv
  have hexp : (n + 1) * p = n * (p + k) + 1 := by
    rw [Nat.mul_add, Nat.add_mul, one_mul, ← hk]
    omega
  have hgrowth : n + 1 < (n + 1) * p := lt_mul_of_one_lt_right (by omega) hp₁
  refine ⟨(n + 1) * p, ⟨hN.even.mul_right _, htwo.trans hgrowth, ?_⟩, hgrowth⟩
  calc
    2 ^ ((n + 1) * p) = 2 ^ (n * (p + k) + 1) := by rw [hexp]
    _ ≡ 2 [MOD (n + 1) * p] := pow_mul_add_one_modEq hperiod (p + k)

/--
**Beeger's theorem.** There are infinitely many even pseudoprimes.

Source: N. G. W. H. Beeger, "On even numbers `m` dividing
`2 ^ m - 2`," American Mathematical Monthly 58 (1951), 553–555.
-/
public theorem evenPseudoprimes_infinite :
    MathlibExt.NumberTheory.evenPseudoprimes.Infinite := by
  have hseed : IsEvenPseudoprime 161038 := ⟨by decide, by decide, by decide +kernel⟩
  intro hfin
  obtain ⟨N, hmax⟩ := hfin.exists_maximal ⟨161038, hseed⟩
  obtain ⟨M, hM, hlt⟩ := exists_larger hmax.prop
  exact hlt.not_ge (hmax.le hM)

end MathlibExt.NumberTheory.EvenPseudoprimesWanted
