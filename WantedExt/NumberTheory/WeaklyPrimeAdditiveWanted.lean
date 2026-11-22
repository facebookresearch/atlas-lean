/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Weakly prime-additive numbers of length 4

Statements from Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*,
INTEGERS 24 (2024), Article A9 (definitions and assumption `(*)` read from arXiv:1903.10668v2).
Lemma 1 (Fermat–Euler) is Mathlib's `Nat.ModEq.pow_totient`, and Theorem 3 (Dirichlet) is
Mathlib's `Nat.infinite_setOfPred_prime_and_eq_mod`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- `n` is a sum `∑_{p ∈ s} p^{e_p}` over a set `s` of `t` distinct prime divisors of `n`, with
positive exponents `e_p`.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Section 1, Definition (after Erdős and Hegyvári). -/
public def IsPrimeDivisorPowerSum (n t : ℕ) : Prop :=
  ∃ s : Finset ℕ, s.card = t ∧ (∀ p ∈ s, p.Prime ∧ p ∣ n) ∧
    ∃ e : ℕ → ℕ, (∀ p ∈ s, 0 < e p) ∧ n = ∑ p ∈ s, p ^ e p

/-- A positive integer `n` is weakly prime-additive if it has at least two distinct prime divisors
and is a sum of positive powers of some distinct prime divisors of `n`.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Section 1, Definition. -/
public def IsWeaklyPrimeAdditive (n : ℕ) : Prop :=
  2 ≤ n.primeFactors.card ∧ ∃ t, IsPrimeDivisorPowerSum n t

/-- The length `κ_n` of a weakly prime-additive number: the least number `t` of distinct prime
divisors of `n` whose positive powers sum to `n`.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Section 1, Definition. -/
public noncomputable def weaklyPrimeAdditiveLength (n : ℕ) : ℕ :=
  sInf {t | IsPrimeDivisorPowerSum n t}

/-- `30 = 2 + 3 + 5^2` is a sum of powers of three distinct prime divisors of `30`.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Section 1, Definition. -/
public theorem isPrimeDivisorPowerSum_thirty : IsPrimeDivisorPowerSum 30 3 := by
  refine ⟨{2, 3, 5}, by decide, ?_, fun p => if p = 5 then 2 else 1, ?_, by decide⟩
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨Nat.prime_two, by norm_num⟩
    · exact ⟨Nat.prime_three, by norm_num⟩
    · exact ⟨Nat.prime_five, by norm_num⟩
  · intro p _
    dsimp only
    split_ifs <;> norm_num

/-- `30` is weakly prime-additive.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Section 1, Definition. -/
public theorem isWeaklyPrimeAdditive_thirty : IsWeaklyPrimeAdditive 30 := by
  refine ⟨?_, 3, isPrimeDivisorPowerSum_thirty⟩
  have h : ({2, 3} : Finset ℕ) ⊆ (30 : ℕ).primeFactors := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by norm_num, by norm_num⟩
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_three, by norm_num, by norm_num⟩
  simpa using Finset.card_le_card h

/-- The length is at most the size of any representation.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Section 1, Definition (minimality of `κ_n`). -/
public theorem weaklyPrimeAdditiveLength_le {n t : ℕ} (h : IsPrimeDivisorPowerSum n t) :
    weaklyPrimeAdditiveLength n ≤ t :=
  Nat.sInf_le h

/-- Under assumption `(*)` (for `1 ≤ a ≤ f` with `gcd(a, f) = 1`, `4 ∣ f`, and an odd prime
`g ∣ f` with Kronecker symbol `(g/a) = -1`, there is a prime `p ≡ a (mod f)` having `g` as a
primitive root), for every positive integer `m` there are infinitely many weakly prime-additive
`n` with `m ∣ n` and `κ_n = 4`. Since `a` is odd, `(g/a)` is the Jacobi symbol.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Theorem 1. -/
public theorem_wanted infinite_weaklyPrimeAdditive_length_four_dvd
    (hstar : ∀ a f g : ℕ, 1 ≤ a → a ≤ f → Nat.Coprime a f → 4 ∣ f → g.Prime → Odd g →
      g ∣ f → jacobiSym g a = -1 →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD f] ∧ IsPrimitiveRoot (g : ZMod p) (p - 1))
    (m : ℕ) (hm : 0 < m) :
    {n : ℕ | m ∣ n ∧ IsWeaklyPrimeAdditive n ∧ weaklyPrimeAdditiveLength n = 4}.Infinite

/-- Under assumption `(*)`, for distinct odd primes `p, q, r` one of which is `≡ 3` or
`5 (mod 8)`, there are infinitely many primes `s` (taken distinct from `p, q, r`) such that
`pqrs ∣ p^a + q^b + r^c + s^d` for infinitely many quadruples of positive integers
`(a, b, c, d)`.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Theorem 2. -/
public theorem_wanted infinite_primes_dvd_four_prime_power_sum
    (hstar : ∀ a f g : ℕ, 1 ≤ a → a ≤ f → Nat.Coprime a f → 4 ∣ f → g.Prime → Odd g →
      g ∣ f → jacobiSym g a = -1 →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD f] ∧ IsPrimitiveRoot (g : ZMod p) (p - 1))
    (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp2 : Odd p) (hq2 : Odd q) (hr2 : Odd r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hmod : p % 8 = 3 ∨ p % 8 = 5 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ r % 8 = 3 ∨ r % 8 = 5) :
    {s : ℕ | s.Prime ∧ s ≠ p ∧ s ≠ q ∧ s ≠ r ∧
      {x : ℕ × ℕ × ℕ × ℕ | 0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2.1 ∧ 0 < x.2.2.2 ∧
        p * q * r * s ∣ p ^ x.1 + q ^ x.2.1 + r ^ x.2.2.1 + s ^ x.2.2.2}.Infinite}.Infinite

/-- Fang and Chen: for a positive integer `m` there are infinitely many shortest weakly
prime-additive numbers `n` (length `κ_n = 3`) with `m ∣ n` if and only if `8 ∤ m`.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Theorem 5 (Fang and Chen, Corollary 1.1). -/
public theorem_wanted infinite_shortest_weaklyPrimeAdditive_dvd_iff (m : ℕ) (hm : 0 < m) :
    {n : ℕ | m ∣ n ∧ IsWeaklyPrimeAdditive n ∧ weaklyPrimeAdditiveLength n = 3}.Infinite ↔
      ¬ 8 ∣ m

/-- Under assumption `(*)`, for every positive integer `m` there are infinitely many weakly
prime-additive `n` with `m ∣ n` and `κ_n ≤ 4`.

Source: Wing Hong Leung, *On the Weakly Prime-Additive Numbers with Length 4*, INTEGERS 24
(2024), Article A9, Theorem 6. -/
public theorem_wanted infinite_weaklyPrimeAdditive_length_le_four_dvd
    (hstar : ∀ a f g : ℕ, 1 ≤ a → a ≤ f → Nat.Coprime a f → 4 ∣ f → g.Prime → Odd g →
      g ∣ f → jacobiSym g a = -1 →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD f] ∧ IsPrimitiveRoot (g : ZMod p) (p - 1))
    (m : ℕ) (hm : 0 < m) :
    {n : ℕ | m ∣ n ∧ IsWeaklyPrimeAdditive n ∧ weaklyPrimeAdditiveLength n ≤ 4}.Infinite

end

end MetaMathlibExt
