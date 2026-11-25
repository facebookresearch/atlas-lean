/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Set.Insert
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial

/-!
# Schatunowsky's theorem and Iwata's generalization

The ATLAS wiki attributes this classification to Schatunowsky, as quoted by Hirofumi Nakai,
Ken Sasaki and Konoka Yoshida in *Schatunowsky-type Theorems for Imaginary Quadratic Integer
Rings of Class Number One*.

A prime whose square lies below `a` must divide `a` if every integer strictly
between `1` and `a` coprime to `a` is prime. A lower bound for the product of these primes
reduces the classification to a finite check. Iwata's generalization gives finiteness for every
fixed bound on the number of prime factors counted with multiplicity.
-/

namespace MetaMathlibExt

namespace nat_iwata_finite

/-- Bertrand's postulate supplies a new prime factor when the primorial cutoff doubles. -/
private theorem mul_primorial_le {m n : ℕ} (hm : m ≠ 0) (hmn : 2 * m ≤ n) :
    (m + 1) * primorial m ≤ primorial n := by
  obtain ⟨p, hp, hmp, hpm⟩ := Nat.bertrand m hm
  have hcop : p.Coprime (primorial m) :=
    hp.coprime_iff_not_dvd.mpr fun h => hmp.not_ge (hp.dvd_primorial_iff.mp h)
  have hdvd := hcop.mul_dvd_of_dvd_of_dvd (hp.dvd_primorial_iff.mpr (hpm.trans hmn))
    (primorial_dvd_primorial (m := m) (by omega : m ≤ n))
  exact (Nat.mul_le_mul_right _ hmp).trans (Nat.le_of_dvd (primorial_pos n) hdvd)

/-- The primorial eventually dominates every fixed multiple of a fixed power. -/
private theorem exists_le_primorial (k C : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, C * (n + 1) ^ k ≤ primorial n := by
  induction k generalizing C with
  | zero => exact ⟨C, fun n hn => by simpa using hn.trans (le_primorial_self (n := n))⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih (C * 2 ^ (k + 1))
    refine ⟨2 * (N + 1), fun n hn => ?_⟩
    let m := n / 2
    have hm : N ≤ m := by dsimp [m]; omega
    calc
      C * (n + 1) ^ (k + 1) ≤ C * (2 * (m + 1)) ^ (k + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [m]; omega) _)
      _ = (m + 1) * (C * 2 ^ (k + 1) * (m + 1) ^ k) := by
        rw [mul_pow, pow_succ (m + 1)]
        ring
      _ ≤ (m + 1) * primorial m := Nat.mul_le_mul_left _ (hN m hm)
      _ ≤ primorial n := mul_primorial_le (by dsimp [m]; omega) (by dsimp [m]; omega)

end nat_iwata_finite

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
    calc
      (n + 1) ^ 2 ≤ (2 * (m + 1)) ^ 2 := Nat.pow_le_pow_left (by dsimp [m]; omega) _
      _ = 4 * (m + 1) ^ 2 := by ring
      _ < 4 * primorial m := Nat.mul_lt_mul_of_pos_left (ih m (by omega) hm) (by decide)
      _ ≤ (m + 1) * primorial m := Nat.mul_le_mul_right _ (by omega)
      _ ≤ primorial n := nat_iwata_finite.mul_primorial_le (by omega) (by dsimp [m]; omega)

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

/-- **Iwata's generalization of Schatunowsky's theorem.** For every natural number $\ell$, there
are only finitely many natural numbers $a$ such that every natural number $b$ with $1 < b < a$
and $\gcd(a, b) = 1$ satisfies $\Omega(b) \le \ell$, where $\Omega(b)$ is the number of prime
factors of $b$ counted with multiplicity.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Theorem 2,
quoting Iwata (`integers-2026-A110-thm-2`). `ℓ = 0` is included (trivially finite). -/
public theorem nat_iwata_finite (ℓ : ℕ) :
    {a : ℕ | ∀ b : ℕ, 1 < b → b < a → Nat.Coprime a b →
      ArithmeticFunction.cardFactors b ≤ ℓ}.Finite := by
  obtain ⟨N, hN⟩ := nat_iwata_finite.exists_le_primorial (ℓ + 1) 2
  refine (Set.finite_Iic (N ^ (ℓ + 1))).subset ?_
  intro a ha
  change a ≤ N ^ (ℓ + 1)
  by_contra! hlarge
  let n := Nat.nthRoot (ℓ + 1) (a - 1)
  have hn : N ≤ n := (Nat.le_nthRoot_iff (by omega)).mpr (by omega)
  -- Every prime up to the cutoff has its (ℓ + 1)-st power strictly below a.
  have hdvd : primorial n ∣ a := by
    rw [primorial_eq_prod_primesLE]
    refine Finset.prod_primes_dvd a (fun _ hp => (Nat.prime_of_mem_primesLE hp).prime) ?_
    intro p hp
    obtain ⟨hpn, hprime⟩ := Nat.mem_primesLE.mp hp
    by_contra h
    have hpow : p ^ (ℓ + 1) ≤ a - 1 := (Nat.le_nthRoot_iff (by omega)).mp hpn
    have hcount := ha (p ^ (ℓ + 1)) (one_lt_pow₀ hprime.one_lt (by omega)) (by omega)
      (hprime.coprime_pow_of_not_dvd h)
    rw [ArithmeticFunction.cardFactors_apply_prime_pow hprime] at hcount
    omega
  have hlo := hN n hn
  have hhi : a - 1 < (n + 1) ^ (ℓ + 1) := Nat.lt_pow_nthRoot_add_one (by omega) _
  have := Nat.le_of_dvd (by omega : 0 < a) hdvd
  omega

end MetaMathlibExt
