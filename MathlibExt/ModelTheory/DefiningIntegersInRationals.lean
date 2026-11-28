/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Set.Operations
import Mathlib.Data.Rat.Lemmas
import MathlibExt.NumberTheory.LegendreSymbol.OddPrimeNonresidue
import MathlibExt.NumberTheory.QuadraticForms.RobinsonTernary

/-!
# Robinson's definition of the integers in the rationals

J. Robinson, "Definability and decision problems in arithmetic", *J. Symbolic Logic* 14 (1949),
Theorem 3.1(i), pp. 106–107: a rational number `N` is an integer if and only if for all rationals
`A` and `B`, if `φ(A, B, 0)` holds and `φ(A, B, M)` implies `φ(A, B, M + 1)` for every rational `M`,
then `φ(A, B, N)` holds, where `φ(A, B, K)` says that `2 + A B K² + B Z² = X² + A Y²` has a
rational solution `X, Y, Z`.

The proof is Robinson's, p. 107 and p. 109. An integer `N` satisfies the formula by induction,
as `φ(A, B, K)` depends only on `K²`. Conversely, for a prime `p ≡ 3 (mod 4)`, Robinson's
Lemma 3 (`Rat.Robinson.lemma_three`) says that `φ(1, p, M)` holds exactly when the denominator of
`M` is odd and prime to `p`; so `A = 1`, `B = p` satisfy the hypothesis, and the denominator of
`N` is odd and prime to `p`. For a prime `p ≡ 1 (mod 4)`, Lemma 5
(`legendreSym.exists_odd_prime_eq_neg_one`) gives an odd prime `q` with `(q / p) = -1`, and
Lemma 4 (`Rat.Robinson.lemma_four`) gives in the same way, with `A = q`, `B = p`, that the
denominator of `N` is prime to `p`. So the denominator of `N` has no prime factor.
-/

public section

namespace MathlibExt.ModelTheory.DefiningIntegersInRationalsWanted

/-- An integer `K` satisfies `φ(A, B, K)` when `φ(A, B, 0)` holds and `φ(A, B, M)` implies
`φ(A, B, M + 1)`. -/
private theorem exists_of_intCast {A B : ℚ}
    (h0 : ∃ X Y Z : ℚ, 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2)
    (hs : ∀ M : ℚ, (∃ X Y Z : ℚ, 2 + A * B * M ^ 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2) →
      ∃ X Y Z : ℚ, 2 + A * B * (M + 1) ^ 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2) (n : ℤ) :
    ∃ X Y Z : ℚ, 2 + A * B * (n : ℚ) ^ 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2 := by
  have hnat : ∀ k : ℕ, ∃ X Y Z : ℚ, 2 + A * B * (k : ℚ) ^ 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2 := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih => simpa using hs k ih
  have hsq : (n : ℚ) ^ 2 = (n.natAbs : ℚ) ^ 2 := by
    rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rw [hsq]
  exact hnat n.natAbs

/-- **Robinson's definition of `ℤ` in `ℚ`.** A rational number `N` is an integer if and only if
for all rationals `A` and `B`: if `2 + B Z² = X² + A Y²` has a rational solution `X, Y, Z`, and
for every rational `M` solvability of `2 + A B M² + B Z² = X² + A Y²` in rationals `X, Y, Z`
implies solvability of `2 + A B (M + 1)² + B Z² = X² + A Y²`, then
`2 + A B N² + B Z² = X² + A Y²` has a rational solution `X, Y, Z`.

This is the formula of J. Robinson, "Definability and decision problems in arithmetic",
J. Symbolic Logic 14 (1949), Theorem 3.1(i), pp. 106–107, transcribed clause by clause; part (ii)
of that theorem draws the consequence that `ℤ` is first-order definable in the field `ℚ`. -/
theorem mem_range_intCast_iff_robinson (N : ℚ) :
    N ∈ Set.range ((↑) : ℤ → ℚ) ↔
      ∀ A B : ℚ,
        ((∃ X Y Z : ℚ, 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2) ∧
            ∀ M : ℚ, (∃ X Y Z : ℚ, 2 + A * B * M ^ 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2) →
              ∃ X Y Z : ℚ, 2 + A * B * (M + 1) ^ 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2) →
          ∃ X Y Z : ℚ, 2 + A * B * N ^ 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2 := by
  constructor
  · rintro ⟨n, rfl⟩ A B ⟨h0, hs⟩
    exact exists_of_intCast h0 hs n
  · intro h
    -- the denominator of `N` is odd and prime to every prime `p ≡ 3 (mod 4)`
    have h3 : ∀ p : ℕ, p.Prime → p % 4 = 3 → Odd N.den ∧ N.den.Coprime p := by
      intro p hp hp4
      have : Fact p.Prime := ⟨hp⟩
      have hL := fun M : ℚ => Rat.Robinson.lemma_three (p := p) hp4 M
      have key : ∀ M : ℚ, (∃ X Y Z : ℚ, 2 + 1 * p * M ^ 2 + p * Z ^ 2 = X ^ 2 + 1 * Y ^ 2) ↔
          Odd M.den ∧ M.den.Coprime p := fun M => by
        simpa only [one_mul] using hL M
      refine (key N).mp (h 1 p ⟨?_, fun M hM => ?_⟩)
      · obtain ⟨X, Y, Z, hXYZ⟩ := (key 0).mpr (by simp)
        exact ⟨X, Y, Z, by simpa using hXYZ⟩
      · rw [key, Rat.add_ofNat_den] at *
        exact hM
    -- the denominator of `N` is prime to every prime `p ≡ 1 (mod 4)`
    have h1 : ∀ p : ℕ, p.Prime → p % 4 = 1 → N.den.Coprime p := by
      intro p hp hp4
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨q, hq, hqo, hqp⟩ := legendreSym.exists_odd_prime_eq_neg_one p hp4
      have : Fact q.Prime := ⟨hq⟩
      have hq2 : q ≠ 2 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr hqo) even_two
      have key : ∀ M : ℚ, (∃ X Y Z : ℚ, 2 + q * p * M ^ 2 + p * Z ^ 2 = X ^ 2 + q * Y ^ 2) ↔
          M.den.Coprime p ∧ M.den.Coprime q := fun M => by
        rw [← Rat.Robinson.lemma_four hp4 hq2 hqp M, mul_comm (q : ℚ) p]
      refine ((key N).mp (h q p ⟨?_, fun M hM => ?_⟩)).1
      · obtain ⟨X, Y, Z, hXYZ⟩ := (key 0).mpr (by simp)
        exact ⟨X, Y, Z, by simpa using hXYZ⟩
      · rw [key, Rat.add_ofNat_den] at *
        exact hM
    -- so the denominator of `N` is `1`
    have hden : N.den = 1 := by
      by_contra hne
      obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd hne
      rcases hℓ.eq_two_or_odd' with rfl | hℓo
      · obtain ⟨hodd, -⟩ := h3 3 Nat.prime_three rfl
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hℓd)
      · have hcop : N.den.Coprime ℓ := by
          rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hℓo) with h4 | h4
          · exact h1 ℓ hℓ h4
          · exact (h3 ℓ hℓ h4).2
        exact hℓ.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm hℓd)
    exact ⟨N.num, Rat.intCast_num_of_den_eq_one hden⟩

end MathlibExt.ModelTheory.DefiningIntegersInRationalsWanted
