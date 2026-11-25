/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.EvenPseudoprime
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Square prime factors of even pseudoprimes

An even pseudoprime is an even `N > 2` with `2 ^ N ≡ 2 [MOD N]`
(`MathlibExt.NumberTheory.IsEvenPseudoprime`). If `p ^ 2 ∣ N` for a prime `p`, then `p` is a
Wieferich prime, `2 ^ (p - 1) ≡ 1 [MOD p ^ 2]`, and `p ≥ 3511`
(`MetaMathlibExt.evenPseudoprime_wieferich_of_sq_dvd`).

## Proof outline

* `p ≠ 2`: otherwise `4 ∣ N`, so `2 ≡ 2 ^ N ≡ 0 [MOD 4]` since `N ≥ 2`.
* Cancelling the unit `2` gives `2 ^ (N - 1) ≡ 1 [MOD p ^ 2]`, and Euler's theorem gives
  `2 ^ (p * (p - 1)) ≡ 1 [MOD p ^ 2]`. So the order of `2` modulo `p ^ 2` divides `N - 1` and
  `p * (p - 1)`. As `p ∣ N`, the order is coprime to `p`, so it divides `p - 1`.
* `N` is even, so `2 ≡ 2 ^ N` is a square modulo `p`, and the second supplement to quadratic
  reciprocity (`ZMod.exists_sq_eq_two_iff`) gives `p % 8 = 1 ∨ p % 8 = 7`.
* A kernel computation shows that no `n < 3511` with `n % 8 = 1 ∨ n % 8 = 7` satisfies
  `2 ^ (n - 1) % n ^ 2 = 1`. Among `1 ≤ n < 3511`, only the Wieferich prime `1093` satisfies
  `2 ^ (n - 1) % n ^ 2 = 1`, and `1093 % 8 = 5`.
-/

public section

namespace MetaMathlibExt

namespace EvenPseudoprimeWieferich

open MathlibExt.NumberTheory

set_option maxRecDepth 20000 in
/-- No `n < 3511` with `n % 8 = 1 ∨ n % 8 = 7` satisfies `2 ^ (n - 1) % n ^ 2 = 1`, checked by
the kernel (`decide +kernel`, with arbitrary-precision arithmetic on numerals). -/
private theorem two_pow_sub_one_mod_sq_ne_one_of_lt :
    ∀ n < 3511, n % 8 = 1 ∨ n % 8 = 7 → 2 ^ (n - 1) % n ^ 2 ≠ 1 := by
  decide +kernel

/-- `p ≠ 2` whenever `p ^ 2` divides an even pseudoprime `N`: otherwise `4 ∣ N`, so
`2 ≡ 2 ^ N ≡ 0 [MOD 4]` since `N ≥ 2`. -/
private theorem ne_two_of_sq_dvd {N p : ℕ} (hN : IsEvenPseudoprime N) (hpN : p ^ 2 ∣ N) :
    p ≠ 2 := by
  rintro rfl
  have h := hN.modeq.of_dvd hpN
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by have := hN.two_lt; omega⟩
  rw [Nat.ModEq, pow_add] at h
  norm_num at h

/-- Every odd prime whose square divides an even pseudoprime `N` is a Wieferich prime: the order
of `2` modulo `p ^ 2` divides both `N - 1` and `p * (p - 1)`, and it is coprime to `p`. -/
private theorem pow_sub_one_modEq_one_of_sq_dvd {N p : ℕ} (hN : IsEvenPseudoprime N)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpN : p ^ 2 ∣ N) : 2 ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  have hN1 : 1 ≤ N := by have := hN.two_lt; omega
  have hcop : Nat.Coprime 2 (p ^ 2) :=
    ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm).pow_right 2
  -- Cancelling `2` in `2 ^ N ≡ 2 [MOD p ^ 2]`.
  have hN' : 2 ^ (N - 1) ≡ 1 [MOD p ^ 2] := by
    refine Nat.ModEq.cancel_left_of_coprime (c := 2) hcop.symm ?_
    rw [← pow_succ', Nat.sub_add_cancel hN1, mul_one]
    exact hN.modeq.of_dvd hpN
  -- Euler's theorem, with `φ (p ^ 2) = p * (p - 1)`.
  have heuler : 2 ^ (p * (p - 1)) ≡ 1 [MOD p ^ 2] := by
    have ht : Nat.totient (p ^ 2) = p * (p - 1) := by
      rw [Nat.totient_prime_pow hp two_pos, show 2 - 1 = 1 from rfl, pow_one]
    simpa [ht] using Nat.ModEq.pow_totient hcop
  have hord₁ : orderOf (2 : ZMod (p ^ 2)) ∣ N - 1 := by
    apply orderOf_dvd_of_pow_eq_one
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hN'
  have hord₂ : orderOf (2 : ZMod (p ^ 2)) ∣ p * (p - 1) := by
    apply orderOf_dvd_of_pow_eq_one
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr heuler
  -- `p ∣ N`, so `p` does not divide `N - 1`.
  have hcopN : Nat.Coprime (N - 1) p := by
    refine Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_)
    have h1 : p ∣ N - (N - 1) := Nat.dvd_sub ((dvd_pow_self p two_ne_zero).trans hpN) h
    rw [Nat.sub_sub_self hN1] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hord : orderOf (2 : ZMod (p ^ 2)) ∣ p - 1 :=
    (Nat.Coprime.coprime_dvd_left hord₁ hcopN).dvd_of_dvd_mul_left hord₂
  rw [← ZMod.natCast_eq_natCast_iff]
  simpa using orderOf_dvd_iff_pow_eq_one.mp hord

/-- Every odd prime `p` dividing an even pseudoprime `N` satisfies `p % 8 = 1 ∨ p % 8 = 7`: since
`N` is even, `2 ≡ 2 ^ N` is a square modulo `p`. -/
private theorem mod_eight_of_dvd {N p : ℕ} (hN : IsEvenPseudoprime N) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpN : p ∣ N) : p % 8 = 1 ∨ p % 8 = 7 := by
  have : Fact p.Prime := ⟨hp⟩
  refine (ZMod.exists_sq_eq_two_iff hp2).mp ?_
  obtain ⟨m, hm⟩ := hN.even
  have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hN.modeq.of_dvd hpN)
  push_cast at h
  exact ⟨2 ^ m, by rw [← pow_add, ← hm, h]⟩

end EvenPseudoprimeWieferich

/-- **Square prime factors of even pseudoprimes are Wieferich primes.** Let $N$ be an even
pseudoprime and $p$ a prime with $p^2 \mid N$. Then $p$ is a Wieferich prime, that is
$2^{p-1} \equiv 1 \pmod{p^2}$, and $p \ge 3511$.

Source: Cheng, Kinlaw and Nguyen, *The Reciprocal Sum of Even Pseudoprimes*, Journal of
Integer Sequences 29 (2026), Article 26.1.3, Lemma 5 (`jis-2026-26.1.3-lem-5`). -/
theorem evenPseudoprime_wieferich_of_sq_dvd {N p : ℕ}
    (hN : MathlibExt.NumberTheory.IsEvenPseudoprime N) (hp : p.Prime) (hpN : p ^ 2 ∣ N) :
    2 ^ (p - 1) ≡ 1 [MOD p ^ 2] ∧ 3511 ≤ p := by
  have hp2 := EvenPseudoprimeWieferich.ne_two_of_sq_dvd hN hpN
  have hwief := EvenPseudoprimeWieferich.pow_sub_one_modEq_one_of_sq_dvd hN hp hp2 hpN
  refine ⟨hwief, ?_⟩
  by_contra hlt
  refine EvenPseudoprimeWieferich.two_pow_sub_one_mod_sq_ne_one_of_lt p (by omega)
    (EvenPseudoprimeWieferich.mod_eight_of_dvd hN hp hp2
      ((dvd_pow_self p two_ne_zero).trans hpN)) ?_
  rw [hwief, Nat.mod_eq_of_lt (Nat.one_lt_pow two_ne_zero hp.one_lt)]

end MetaMathlibExt
