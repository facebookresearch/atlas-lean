/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WeaklyPrimeAdditive

/-! # Tests for weakly prime-additive multiples -/

namespace MathlibExtTest.WeaklyPrimeAdditive

open MetaMathlibExt

-- A prime power has a one-term representation. Weak prime-additivity also requires two primes.
example : weaklyPrimeAdditiveLength 8 = 1 ∧ ¬IsWeaklyPrimeAdditive 8 := by
  have h : IsPrimeDivisorPowerSum 8 1 := by
    refine ⟨{2}, by simp, ?_, fun _ => 3, by decide, by decide⟩
    simpa using (show Nat.Prime 2 ∧ 2 ∣ 8 by decide)
  have hmin : IsPrimeDivisorPowerSum 8 (weaklyPrimeAdditiveLength 8) :=
    Nat.sInf_mem (s := {t | IsPrimeDivisorPowerSum 8 t}) ⟨1, h⟩
  have hpos : weaklyPrimeAdditiveLength 8 ≠ 0 := by
    intro hz
    rw [hz] at hmin
    obtain ⟨s, hs, _, e, _, hn⟩ := hmin
    simp [Finset.card_eq_zero.mp hs] at hn
  have hle := weaklyPrimeAdditiveLength_le h
  refine ⟨by omega, fun hw => ?_⟩
  have hcard := hw.1
  rw [show 8 = 2 ^ 3 by decide, Nat.primeFactors_prime_pow (by decide) Nat.prime_two] at hcard
  simp at hcard

-- The conclusion gives witnesses beyond any bound even for a modulus divisible by eight.
example (H : ∀ a f g : ℕ, 1 ≤ a → a ≤ f → Nat.Coprime a f → 4 ∣ f → g.Prime → Odd g →
    g ∣ f → jacobiSym g a = -1 →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD f] ∧ IsPrimitiveRoot (g : ZMod p) (p - 1)) (B : ℕ) :
    ∃ n > B, 8 ∣ n ∧ IsWeaklyPrimeAdditive n ∧ weaklyPrimeAdditiveLength n ≤ 4 := by
  obtain ⟨n, hn, hB⟩ := Set.infinite_iff_exists_gt.mp
    (infinite_weaklyPrimeAdditive_length_le_four_dvd H 8 (by decide)) B
  exact ⟨n, hB, hn⟩

-- A factor of four and an odd prime factor can both be prescribed.
example (B : ℕ) : ∃ n > B, 12 ∣ n ∧ IsWeaklyPrimeAdditive n ∧ weaklyPrimeAdditiveLength n = 3 := by
  obtain ⟨n, hn, hB⟩ := Set.infinite_iff_exists_gt.mp
    ((infinite_shortest_weaklyPrimeAdditive_dvd_iff 12 (by decide)).mpr (by decide)) B
  exact ⟨n, hB, hn⟩

-- At the next power of two the set of shortest multiples is finite.
example : {n : ℕ | 8 ∣ n ∧ IsWeaklyPrimeAdditive n ∧ weaklyPrimeAdditiveLength n = 3}.Finite := by
  apply Set.not_infinite.mp
  intro h
  exact (infinite_shortest_weaklyPrimeAdditive_dvd_iff 8 (by decide)).mp h dvd_rfl

section

variable (H : ∀ a f g : ℕ, 1 ≤ a → a ≤ f → Nat.Coprime a f → 4 ∣ f → g.Prime → Odd g →
  g ∣ f → jacobiSym g a = -1 →
  ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD f] ∧ IsPrimitiveRoot (g : ZMod p) (p - 1))

-- At the smallest positive modulus there are infinitely many numbers of exact length four.
example : {n : ℕ | IsWeaklyPrimeAdditive n ∧ weaklyPrimeAdditiveLength n = 4}.Infinite := by
  simpa using infinite_weaklyPrimeAdditive_length_four_dvd H 1 (by decide)

-- Divisibility by both eight and an odd prime is compatible with exact length four.
example (B : ℕ) : ∃ n > B, 24 ∣ n ∧ IsWeaklyPrimeAdditive n ∧ weaklyPrimeAdditiveLength n = 4 := by
  obtain ⟨n, hn, hB⟩ := Set.infinite_iff_exists_gt.mp
    (infinite_weaklyPrimeAdditive_length_four_dvd H 24 (by decide)) B
  exact ⟨n, hB, hn⟩

end

end MathlibExtTest.WeaklyPrimeAdditive
