/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.FieldTheory.Finite.Basic

/-!
# Nine divides the exponent

For odd `m > 1` satisfying `m ∣ a ^ m + 1`, the least prime factor of `m` divides `a + 1`.
Applying this first with base 2 and then with base 8 gives two factors of 3 in the exponent.
-/

namespace MetaMathlibExt

namespace nine_dvd_of_three_mul_dvd_two_pow_add_one

private theorem minFac_dvd_add_one {m a : ℕ} (hm : 1 < m) (ho : Odd m)
    (h : m ∣ a ^ m + 1) : m.minFac ∣ a + 1 := by
  let p := m.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have : Fact p.Prime := ⟨hp⟩
  have hz := (ZMod.natCast_eq_zero_iff _ p).2 ((Nat.minFac_dvd m).trans h)
  push_cast at hz
  have hpow : (-(a : ZMod p)) ^ m = 1 := by
    rw [ho.neg_pow, neg_eq_iff_add_eq_zero]
    simpa only [add_comm] using hz
  have hunit := IsUnit.of_pow_eq_one hpow (by omega)
  have hcop : m.Coprime (p - 1) :=
    Nat.coprime_of_lt_minFac (Nat.sub_ne_zero_of_lt hp.one_lt) (Nat.sub_lt hp.pos (by decide))
  have heq : -(a : ZMod p) = 1 := orderOf_eq_one_iff.mp <|
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hpow)
      (ZMod.orderOf_dvd_card_sub_one hunit.ne_zero)
  apply (ZMod.natCast_eq_zero_iff _ p).1
  simpa [add_comm, neg_eq_iff_add_eq_zero] using heq

end nine_dvd_of_three_mul_dvd_two_pow_add_one

open nine_dvd_of_three_mul_dvd_two_pow_add_one in
/-- **Nine divides $n$ when $n > 3$ and $3n$ divides $2^n + 1$.** Let $n > 3$ be a natural
number. If $3n$ divides $2^n + 1$, then $9$ divides $n$.

For odd $n$ the hypothesis says that $n$ divides the integer $(2^n + 1)/3$, which is the form
in the paper; for even $n$ it never holds, since $3$ does not divide $2^n + 1$.

Source: Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard
Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Lemma 4
(`integers-2026-A107-lem-4`), quoting [3]. -/
public theorem nine_dvd_of_three_mul_dvd_two_pow_add_one (n : ℕ) (hn : 3 < n)
    (h : 3 * n ∣ 2 ^ n + 1) : 9 ∣ n := by
  have hd : n ∣ 2 ^ n + 1 := (dvd_mul_left n 3).trans h
  have ho : Odd n := (even_two.pow_of_ne_zero (by omega : n ≠ 0)).add_one.of_dvd_nat hd
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  have hmin : n.minFac = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
    (minFac_dvd_add_one (by omega) ho hd)
  obtain ⟨m, rfl⟩ : 3 ∣ n := hmin ▸ Nat.minFac_dvd n
  have hm : m ∣ 8 ^ m + 1 := by
    rw [pow_mul] at hd
    exact (dvd_mul_left m 3).trans hd
  have hmin' : m.minFac ∣ 3 ^ 2 :=
    minFac_dvd_add_one (by omega) (Nat.odd_mul.mp ho).2 hm
  have heq := Nat.prime_eq_prime_of_dvd_pow (Nat.minFac_prime (by omega : m ≠ 1))
    Nat.prime_three hmin'
  have h3 : 3 ∣ m := heq ▸ Nat.minFac_dvd m
  exact Nat.mul_dvd_mul_left 3 h3

end MetaMathlibExt
