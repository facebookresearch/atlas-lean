/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RFubiniPeriodicity
import Mathlib.Tactic.NormNum

open MetaMathlibExt ArithmeticFunction

-- Modulo `4 = 2²`: `λ(4) = 2` and `R = 2`, so the `2`-Fubini numbers `1, 1, 2, 10, 62, 466, …`
-- repeat with period `2` modulo `4` from `n = 3` on.
example (n : ℕ) (hn : 3 ≤ n) :
    let rFubini : ℕ → ℕ := fun m => ∑ k ∈ Finset.range (m + 1),
      Nat.card { f : Fin m → Fin k // Function.Surjective f ∧
        ∀ i j : Fin m, (i : ℕ) < 2 → (j : ℕ) < 2 → f i = f j → i = j }
    rFubini (n + 2) ≡ rFubini n [MOD 4] := by
  have hcar : carmichael 4 = 2 := by
    simpa using carmichael_two_pow_of_le_two (n := 2) le_rfl
  have hfac : (4 : ℕ).factorization = Finsupp.single 2 2 := by
    simpa using Nat.prime_two.factorization_pow (k := 2)
  have hR : (4 : ℕ).factorization.support.sup (4 : ℕ).factorization = 2 := by
    rw [hfac, Finsupp.support_single _ two_ne_zero, Finset.sup_singleton,
      Finsupp.single_eq_same]
  have h := rFubini_add_carmichael_modEq 4 2 n (by norm_num) (by omega)
  rw [hcar] at h
  exact h

-- Modulo the prime `2`: `λ(2) = 1` and `R = 1`, so the parity of the `3`-Fubini numbers is
-- constant from `n = 3` on.
example (n : ℕ) (hn : 3 ≤ n) :
    let rFubini : ℕ → ℕ := fun m => ∑ k ∈ Finset.range (m + 1),
      Nat.card { f : Fin m → Fin k // Function.Surjective f ∧
        ∀ i j : Fin m, (i : ℕ) < 3 → (j : ℕ) < 3 → f i = f j → i = j }
    rFubini (n + 1) ≡ rFubini n [MOD 2] := by
  have hR : (2 : ℕ).factorization.support.sup (2 : ℕ).factorization = 1 := by
    rw [Nat.prime_two.factorization, Finsupp.support_single _ one_ne_zero,
      Finset.sup_singleton, Finsupp.single_eq_same]
  have h := rFubini_add_carmichael_modEq 2 3 n (by norm_num) (by omega)
  rw [carmichael_two] at h
  exact h

-- For `K = 0` the bound is `n ≥ r - 1` and `λ(0) = 0`, so the congruence is equality.
example (r n : ℕ) (hr : 1 ≤ r) (hn : r - 1 ≤ n) :
    let rFubini : ℕ → ℕ := fun m => ∑ k ∈ Finset.range (m + 1),
      Nat.card { f : Fin m → Fin k // Function.Surjective f ∧
        ∀ i j : Fin m, (i : ℕ) < r → (j : ℕ) < r → f i = f j → i = j }
    rFubini (n + carmichael 0) ≡ rFubini n [MOD 0] :=
  rFubini_add_carmichael_modEq 0 r n hr (by simpa using hn)

-- The Fubini numbers `1, 1, 3, 13, 75, 541, …`: modulo `4 = 2²`, where `λ(4) = 2` and `R = 2`,
-- they repeat with period `2` from `n = 2` on.
example (n : ℕ) (hn : 2 ≤ n) : fubiniNumber (n + 2) ≡ fubiniNumber n [MOD 4] := by
  have hcar : carmichael 4 = 2 := by
    simpa using carmichael_two_pow_of_le_two (n := 2) le_rfl
  have hfac : (4 : ℕ).factorization = Finsupp.single 2 2 := by
    simpa using Nat.prime_two.factorization_pow (k := 2)
  have hR : (4 : ℕ).factorization.support.sup (4 : ℕ).factorization = 2 := by
    rw [hfac, Finsupp.support_single _ two_ne_zero, Finset.sup_singleton,
      Finsupp.single_eq_same]
  have h := fubiniNumber_add_carmichael_modEq 4 n (by omega)
  rw [hcar] at h
  exact h

-- Modulo the prime `3`, where `λ(3) = 2` and `R = 1`, the Fubini numbers alternate between `1`
-- and `0` from `n = 1` on.
example (n : ℕ) (hn : 1 ≤ n) : fubiniNumber (n + 2) ≡ fubiniNumber n [MOD 3] := by
  have hR : (3 : ℕ).factorization.support.sup (3 : ℕ).factorization = 1 := by
    rw [Nat.prime_three.factorization, Finsupp.support_single _ one_ne_zero,
      Finset.sup_singleton, Finsupp.single_eq_same]
  have h := fubiniNumber_add_carmichael_modEq 3 n (by omega)
  rw [carmichael_of_prime Nat.prime_three] at h
  exact h

-- For `K = 0` the bound is `n ≥ 0` and `λ(0) = 0`, so the congruence is equality.
example (n : ℕ) : fubiniNumber (n + carmichael 0) ≡ fubiniNumber n [MOD 0] :=
  fubiniNumber_add_carmichael_modEq 0 n (by simp)

-- Proposition 4 modulo `4 = 2²`, where `λ(4) = 2` and `R = 2`: every residue `a < 4`, the
-- non-units `0` and `2` included, satisfies `a² ≡ a⁴ (mod 4)`.
example (a : ℕ) (ha : a < 4) : a ^ 2 ≡ a ^ 4 [MOD 4] := by
  have hcar : carmichael 4 = 2 := by
    simpa using carmichael_two_pow_of_le_two (n := 2) le_rfl
  have hfac : (4 : ℕ).factorization = Finsupp.single 2 2 := by
    simpa using Nat.prime_two.factorization_pow (k := 2)
  have hR : (4 : ℕ).factorization.support.sup (4 : ℕ).factorization = 2 := by
    rw [hfac, Finsupp.support_single _ two_ne_zero, Finset.sup_singleton,
      Finsupp.single_eq_same]
  have h := pow_add_carmichael_modEq_of_lt 4 a ha
  simp only [hR, hcar] at h
  exact h

-- The exponent `R` cannot be lowered to `0`: the non-unit `2` has `2⁰ ≢ 2^λ(4) (mod 4)`.
example : ¬ 2 ^ 0 ≡ 2 ^ 2 [MOD 4] := by decide

-- Modulo a prime `p`, where `λ(p) = p - 1` and `R = 1`, Proposition 4 is Fermat's little theorem
-- `a ≡ a ^ p (mod p)`.
example (p a : ℕ) (hp : p.Prime) (ha : a < p) : a ≡ a ^ p [MOD p] := by
  have hR : p.factorization.support.sup p.factorization = 1 := by
    rw [hp.factorization, Finsupp.support_single _ one_ne_zero, Finset.sup_singleton,
      Finsupp.single_eq_same]
  have h := pow_add_carmichael_modEq_of_lt p a ha
  simp only [hR, carmichael_of_prime hp, Nat.sub_add_cancel hp.one_le, pow_one] at h
  exact h
