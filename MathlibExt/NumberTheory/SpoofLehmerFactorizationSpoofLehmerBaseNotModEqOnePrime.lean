/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import MathlibExt.NumberTheory.SpoofLehmerFactorization
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.ModEq
import MathlibExt.NumberTheory.SpoofLehmerResidues

/-!
# Primes dividing the evaluation of a spoof Lehmer factorization

The main result is `spoofLehmer_base_not_modEq_one_prime`: if a prime divides the spoof
evaluation of a nontrivial spoof Lehmer factorization with all exponents one, then no base is
one modulo that prime; moreover, an even such factorization has all bases even.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Corollary 2.
-/

namespace MetaMathlibExt

/-- **Primes dividing the evaluation of a spoof Lehmer factorization.** Let $x_1, \dots, x_r$ be
natural numbers and let $F = x_1 \cdots x_r$ be the spoof factorization with these bases, all with
exponent $1$. Suppose $F$ is a nontrivial spoof $k$-Lehmer factorization for some integer $k$. If
$p$ is a prime dividing the spoof evaluation $\tilde e(F)$, then $x_i \not\equiv 1 \pmod p$ for
every $i$. Moreover, if $F$ is even (not every base is odd), then every base $x_i$ is even.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Corollary 2 (`integers-2026-A33-cor-2`). -/
public theorem spoofLehmer_base_not_modEq_one_prime (x : Multiset ℕ) (k : ℤ)
    (hL : IsSpoofLehmer k (spoofOfBases x))
    (hnt : ¬ IsTrivialSpoof (spoofOfBases x)) :
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ spoofEval (spoofOfBases x) →
      ∀ a ∈ x, ¬ a ≡ 1 [MOD p]) ∧
    (¬ IsOddSpoof (spoofOfBases x) → ∀ a ∈ x, Even a) := by
  have part1 : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ spoofEval (spoofOfBases x) →
      ∀ a ∈ x, ¬ a ≡ 1 [MOD p] := by
    intro p hp hdvd a ha hmod
    have hunit : ¬ IsUnit (p : ℤ) := by
      rw [Int.isUnit_iff]
      have h2 := hp.two_le
      omega
    have hmodZ : (a : ℤ) ≡ 1 [ZMOD (p : ℤ)] := by
      simpa using Int.natCast_modEq_iff.mpr hmod
    exact spoofLehmer_base_not_modEq_one x k hL hnt (p : ℤ) hdvd hunit a ha hmodZ
  refine ⟨part1, fun hnotOdd a ha => ?_⟩
  simp only [IsOddSpoof] at hnotOdd
  obtain ⟨q, hq⟩ := not_forall.mp hnotOdd
  obtain ⟨hqF, hqodd⟩ := not_imp.mp hq
  obtain ⟨b, hb, hqb⟩ := Multiset.mem_map.mp hqF
  subst hqb
  dsimp only at hqodd
  have hbeven : Even b := Nat.not_odd_iff_even.mp hqodd
  have hbdvd : (b : ℤ) ∣ spoofEval (spoofOfBases x) := by
    apply Multiset.dvd_prod
    exact Multiset.mem_map.mpr ⟨(b, 1), Multiset.mem_map_of_mem _ hb, by simp⟩
  have h2dvd : (2 : ℤ) ∣ spoofEval (spoofOfBases x) :=
    (Int.natCast_dvd_natCast.mpr (even_iff_two_dvd.mp hbeven)).trans hbdvd
  have hmod2 : ¬ a ≡ 1 [MOD 2] :=
    part1 2 Nat.prime_two h2dvd a ha
  by_contra hne
  rw [Nat.not_even_iff_odd] at hne
  apply hmod2
  have h := Nat.odd_iff.mp hne
  change a % 2 = 1 % 2
  exact h.trans (by decide)

end MetaMathlibExt
