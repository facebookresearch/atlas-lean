/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Set.Insert
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial

/-!
# Schatunowsky's theorem

The ATLAS wiki attributes this classification to Schatunowsky, as quoted by Hirofumi Nakai,
Ken Sasaki and Konoka Yoshida in *Schatunowsky-type Theorems for Imaginary Quadratic Integer
Rings of Class Number One*.

A prime whose square lies below `a` must divide `a` if every integer strictly
between `1` and `a` coprime to `a` is prime. A lower bound for the product of these primes
reduces the classification to a finite check.
-/

namespace MetaMathlibExt

/-- For `n ≥ 7`, the product of the primes up to `n` exceeds the next square. -/
private theorem succ_sq_lt_primorial (n : ℕ) (hn : 7 ≤ n) : (n + 1) ^ 2 < primorial n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hsmall : n < 14
    · calc
        (n + 1) ^ 2 ≤ 14 ^ 2 := Nat.pow_le_pow_left (by omega) _
        _ < primorial 7 := by decide
        _ ≤ primorial n := primorial_mono hn
    let m := n / 2
    have hm : 7 ≤ m := by dsimp [m]; omega
    obtain ⟨p, hp, hmp, hpm⟩ := Nat.bertrand m (by omega)
    have hpn : p ≤ n := by dsimp [m] at hpm; omega
    have hcop : p.Coprime (primorial m) :=
      hp.coprime_iff_not_dvd.mpr fun h => hmp.not_ge (hp.dvd_primorial_iff.mp h)
    have hdvd := hcop.mul_dvd_of_dvd_of_dvd (hp.dvd_primorial_iff.mpr hpn)
      (primorial_dvd_primorial (m := m) (by omega : m ≤ n))
    calc
      (n + 1) ^ 2 ≤ (2 * (m + 1)) ^ 2 := Nat.pow_le_pow_left (by dsimp [m]; omega) _
      _ = 4 * (m + 1) ^ 2 := by ring
      _ < 4 * primorial m := Nat.mul_lt_mul_of_pos_left (ih m (by omega) hm) (by decide)
      _ ≤ p * primorial m := Nat.mul_le_mul_right _ (by omega)
      _ ≤ primorial n := Nat.le_of_dvd (primorial_pos n) hdvd

private theorem lt_fifty_of_coprimes_prime {a : ℕ}
    (ha : ∀ b : ℕ, 1 < b → b < a → a.Coprime b → b.Prime) : a < 50 := by
  by_contra! hlarge
  let n := (a - 1).sqrt
  have hn : 7 ≤ n := Nat.le_sqrt'.mpr (by omega)
  have hdvd : primorial n ∣ a := by
    rw [primorial_eq_prod_primesLE]
    refine Finset.prod_primes_dvd a (fun _ hp => (Nat.prime_of_mem_primesLE hp).prime) ?_
    intro p hp
    obtain ⟨hpn, hprime⟩ := Nat.mem_primesLE.mp hp
    by_contra h
    have hsquare : p ^ 2 ≤ a - 1 := Nat.le_sqrt'.mp hpn
    exact Nat.Prime.not_prime_pow (by decide : 2 ≤ 2)
      (ha (p ^ 2) (one_lt_pow₀ hprime.one_lt (by decide)) (by omega)
        (hprime.coprime_pow_of_not_dvd h))
  have hlower := succ_sq_lt_primorial n hn
  have hupper : a - 1 < (n + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have := Nat.le_of_dvd (by omega : 0 < a) hdvd
  omega

/-- **Schatunowsky's theorem.** The natural numbers `a ≥ 2` for which every integer strictly
between `1` and `a` coprime to `a` is prime are exactly `2, 3, 4, 6, 8, 12, 18, 24, 30`.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Theorem 1,
quoting Schatunowsky (`integers-2026-A110-thm-1`). -/
public theorem nat_schatunowsky :
    {a : ℕ | 2 ≤ a ∧ ∀ b : ℕ, 1 < b → b < a → Nat.Coprime a b → b.Prime} =
      {2, 3, 4, 6, 8, 12, 18, 24, 30} := by
  ext a
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  by_cases h : a < 50
  · rw [show (∀ b : ℕ, 1 < b → b < a → a.Coprime b → b.Prime) ↔
        (∀ b < a, 1 < b → a.Coprime b → b.Prime) from forall_congr' fun _ => ⟨flip, flip⟩]
    decide +revert
  · constructor
    · rintro ⟨_, ha⟩
      exact (h (lt_fifty_of_coprimes_prime ha)).elim
    · omega

end MetaMathlibExt
