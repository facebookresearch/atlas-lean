/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.Simproc.Factors
import MathlibExt.NumberTheory.Recurrences.FibonacciPrimitivePart

open MetaMathlibExt ArithmeticFunction

namespace MetaMathlibExtTest.FibonacciPrimitivePart

private theorem moebius_four : moebius 4 = 0 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, moebius_apply_prime_pow Nat.prime_two (by norm_num)]
  norm_num

private theorem moebius_six : moebius 6 = 1 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    moebius_apply_prime Nat.prime_two, moebius_apply_prime Nat.prime_three]
  norm_num

private theorem fibCyclotomicValue_three : fibCyclotomicValue 3 = 2 := by
  have hd : Nat.divisors 3 = {1, 3} := by decide
  norm_num [fibCyclotomicValue, hd, moebius_apply_prime Nat.prime_three]

private theorem fibCyclotomicValue_four : fibCyclotomicValue 4 = 3 := by
  have hd : Nat.divisors 4 = {1, 2, 4} := by decide
  norm_num [fibCyclotomicValue, hd, moebius_apply_prime Nat.prime_two, moebius_four]

private theorem fibCyclotomicValue_five : fibCyclotomicValue 5 = 5 := by
  have hd : Nat.divisors 5 = {1, 5} := by decide
  norm_num [fibCyclotomicValue, hd, moebius_apply_prime Nat.prime_five]

private theorem fibCyclotomicValue_six : fibCyclotomicValue 6 = 4 := by
  have hd : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  norm_num [fibCyclotomicValue, hd, moebius_apply_prime Nat.prime_two,
    moebius_apply_prime Nat.prime_three, moebius_six]

private theorem fibCyclotomicValue_twelve : fibCyclotomicValue 12 = 6 := by
  have hd : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
  norm_num [fibCyclotomicValue, hd, moebius_apply_prime Nat.prime_two,
    moebius_apply_prime Nat.prime_three, moebius_four]

private theorem fibCyclotomicValue_twentyFive : fibCyclotomicValue 25 = 15005 := by
  have hd : Nat.divisors 25 = {1, 5, 25} := by decide
  norm_num [fibCyclotomicValue, hd, moebius_apply_prime Nat.prime_five]

private theorem fibPrimitivePart_prime {m p : ℕ} (hp : p.Prime) (hfib : Nat.fib m = p)
    (hz : fibEntryPoint p = m) : fibPrimitivePart m = p := by
  simp [fibPrimitivePart, hfib, Nat.Prime.primeFactors hp, Finset.filter_singleton, hz,
    hp.factorization_self]

/-- Luca's lemma applies to `I = {25}` and `J = {5}`: the quotient is
`Φ_25 / Φ_5 = 15005 / 5 = 3001`. -/
example : ∃ e : Multiset (ℕ × ℕ),
    e.map Prod.fst = (((({5} : Multiset ℕ).map fibPrimitivePart).prod.primeFactorsList :
      Multiset ℕ)) ∧
      e.map (fun pk => pk.1 ^ pk.2 * fibEntryPoint pk.1) ≤ {25} :=
  exists_injection_primeFactors_fibPrimitivePart {25} {5} (by simp) (by simp) (by simp)
    ⟨3001, by simp [fibCyclotomicValue_twentyFive, fibCyclotomicValue_five]; norm_num⟩

/-- For `I = {25}` and `J = {5}` the conclusion forces `e = {(5, 1)}`: the single prime factor
`5` of `Ψ_5 = F_5 = 5` goes to `25 = 5^1 z(5)`. -/
example (e : Multiset (ℕ × ℕ))
    (h1 : e.map Prod.fst = (((({5} : Multiset ℕ).map fibPrimitivePart).prod.primeFactorsList :
      Multiset ℕ)))
    (h2 : e.map (fun pk => pk.1 ^ pk.2 * fibEntryPoint pk.1) ≤ {25}) : e = {(5, 1)} := by
  have hfst : e.map Prod.fst = {5} := by
    rw [h1, Multiset.map_singleton, Multiset.prod_singleton,
      fibPrimitivePart_prime Nat.prime_five (by decide) fibEntryPoint_five,
      Nat.primeFactorsList_prime Nat.prime_five, Multiset.coe_singleton]
  obtain ⟨⟨p, k⟩, rfl⟩ := Multiset.card_eq_one.mp (by simpa using congrArg Multiset.card hfst)
  simp only [Multiset.map_singleton, Multiset.singleton_inj] at hfst
  subst hfst
  simp only [Multiset.map_singleton, Multiset.singleton_le, Multiset.mem_singleton,
    fibEntryPoint_five] at h2
  have hk : 5 ^ k = 5 ^ 1 := by omega
  rw [show k = 1 from Nat.pow_right_injective (by norm_num : 2 ≤ 5) hk]

/-- The hypothesis `n ≠ 6` on `I` is needed: `Φ_6 / Φ_3^2 = 4 / 4 = 1`, but the two prime
factors of `Ψ_3^2 = 4` cannot both be sent to the single element of `I = {6}`. -/
example : (({6} : Multiset ℕ).map fibCyclotomicValue).prod /
      (({3, 3} : Multiset ℕ).map fibCyclotomicValue).prod = (1 : ℕ) ∧
    ¬ ∃ e : Multiset (ℕ × ℕ),
      e.map Prod.fst = (((({3, 3} : Multiset ℕ).map fibPrimitivePart).prod.primeFactorsList :
        Multiset ℕ)) ∧
        e.map (fun pk => pk.1 ^ pk.2 * fibEntryPoint pk.1) ≤ {6} := by
  have hΨ : fibPrimitivePart 3 = 2 :=
    fibPrimitivePart_prime Nat.prime_two (by decide) fibEntryPoint_two
  refine ⟨by simp [fibCyclotomicValue_six, fibCyclotomicValue_three]; norm_num, ?_⟩
  rintro ⟨e, h1, h2⟩
  have hcard := congrArg Multiset.card h1
  have hle := Multiset.card_le_card h2
  simp [hΨ, Nat.primeFactorsList_ofNat] at hcard hle
  omega

/-- The hypothesis `n ≠ 12` on `I` is needed: `Φ_12 / (Φ_3 Φ_4) = 6 / 6 = 1`, but the prime
factors `2` and `3` of `Ψ_3 Ψ_4 = 6` cannot both be sent to the single element of `I = {12}`. -/
example : (({12} : Multiset ℕ).map fibCyclotomicValue).prod /
      (({3, 4} : Multiset ℕ).map fibCyclotomicValue).prod = (1 : ℕ) ∧
    ¬ ∃ e : Multiset (ℕ × ℕ),
      e.map Prod.fst = (((({3, 4} : Multiset ℕ).map fibPrimitivePart).prod.primeFactorsList :
        Multiset ℕ)) ∧
        e.map (fun pk => pk.1 ^ pk.2 * fibEntryPoint pk.1) ≤ {12} := by
  have hΨ3 : fibPrimitivePart 3 = 2 :=
    fibPrimitivePart_prime Nat.prime_two (by decide) fibEntryPoint_two
  have hΨ4 : fibPrimitivePart 4 = 3 :=
    fibPrimitivePart_prime Nat.prime_three (by decide) fibEntryPoint_three
  refine ⟨by
    simp [fibCyclotomicValue_twelve, fibCyclotomicValue_three, fibCyclotomicValue_four]
    norm_num, ?_⟩
  rintro ⟨e, h1, h2⟩
  have hcard := congrArg Multiset.card h1
  have hle := Multiset.card_le_card h2
  simp [hΨ3, hΨ4, Nat.primeFactorsList_ofNat] at hcard hle
  omega

end MetaMathlibExtTest.FibonacciPrimitivePart
