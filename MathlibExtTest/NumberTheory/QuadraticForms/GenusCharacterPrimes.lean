/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.GenusCharacterPrimes
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Simproc.Factors
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# Tests for `MetaMathlibExt.GenusCharacterPrimes`

Values of the $2$-adic genus character in each of its three cases; Problem 38 for a sign system
of product $-1$ at $D = 5$; Problem 39 for the two primes $3$ and $7$ at $D = -20$ and for
$q = 2$ at $D = -15$; and the combined statement at the fundamental discriminants $-15$ (odd),
$-20$ (with $\xi$) and $8$ (positive, with $\eta$).
-/

@[expose] public section

namespace MetaMathlibExt.GenusCharacterPrimesTest

#check @genusCharTwo
#check @exists_prime_genusCharacters
#check @exists_discrim_eq_of_genusCharacters
#check @exists_prime_genusCharacters_discrim_eq

-- `D = -20`, `D/4 = -5 ≡ 3 (mod 4)`: the character is `χ₄`.
example : genusCharTwo (-20) 3 = -1 ∧ genusCharTwo (-20) 5 = 1 := by decide

-- `D = 8`, `D/4 = 2 ≡ 2 (mod 8)`: the character is `χ₈`.
example : genusCharTwo 8 3 = -1 ∧ genusCharTwo 8 7 = 1 := by decide

-- `D = -8`, `D/4 = -2 ≡ 6 (mod 8)`: the character is `χ₈'`.
example : genusCharTwo (-8) 3 = 1 ∧ genusCharTwo (-8) 5 = -1 := by decide

-- `D` odd: the character is trivial.
example : genusCharTwo (-15) 7 = 1 := by decide

-- An explicit instance of the conclusion for `D = -15` and the trivial genus: `q = 19` has
-- `(19/3) = (19/5) = 1`, and `17² - 4·19·4 = -15`.
example : jacobiSym 19 3 = 1 ∧ jacobiSym 19 5 = 1 ∧ discrim (19 : ℤ) 17 4 = -15 := by
  refine ⟨?_, ?_, by decide⟩ <;> norm_num

theorem isFundamentalDiscriminant_neg_fifteen : IsFundamentalDiscriminant (-15) :=
  Or.inl ⟨Int.squarefree_natAbs.1 (by simp [Nat.squarefree_iff_nodup_primeFactorsList]),
    by decide⟩

theorem isFundamentalDiscriminant_neg_twenty : IsFundamentalDiscriminant (-20) :=
  Or.inr ⟨-5, by norm_num,
    Int.squarefree_natAbs.1 (by simp [Nat.squarefree_iff_nodup_primeFactorsList]), by decide⟩

theorem isFundamentalDiscriminant_five : IsFundamentalDiscriminant 5 :=
  Or.inl ⟨Int.squarefree_natAbs.1 (by simp [Nat.squarefree_iff_nodup_primeFactorsList]),
    by decide⟩

-- Problem 38 with a sign system of product `-1`: a prime `q` with `(q/5) = -1`.
example : ∃ q : ℕ, q.Prime ∧ jacobiSym (q : ℤ) 5 = -1 := by
  have h5 : (5 : ℕ).primeFactors = {5} := by simp [Nat.primeFactors]
  obtain ⟨q, hq, -, hodd, -⟩ := exists_prime_genusCharacters (D := 5)
    isFundamentalDiscriminant_five (fun _ => -1) (fun _ _ => Or.inr rfl)
  exact ⟨q, hq, hodd 5 (by simp [h5]) (by norm_num)⟩

-- Problem 39 for every admissible prime: at `D = -20` with `s ≡ -1`, both `3` and `7`.
example : (∃ b c : ℤ, discrim (3 : ℤ) b c = -20) ∧ ∃ b c : ℤ, discrim (7 : ℤ) b c = -20 := by
  have h20 : (20 : ℕ).primeFactors = {2, 5} := by simp [Nat.primeFactors]
  have hD : (-20 : ℤ).natAbs = 20 := rfl
  have hprod : ∏ p ∈ (-20 : ℤ).natAbs.primeFactors, (fun _ => (-1 : ℤ)) p = 1 := by
    simp [hD, h20]
  constructor
  · exact_mod_cast exists_discrim_eq_of_genusCharacters isFundamentalDiscriminant_neg_twenty
      (fun _ => -1) hprod (q := 3) Nat.prime_three (by rw [hD]; norm_num)
      (fun p hp hp2 => by
        rw [hD, h20] at hp
        rcases Finset.mem_insert.1 hp with rfl | hp
        · exact absurd rfl hp2
        · rw [Finset.mem_singleton.1 hp]; norm_num)
      (fun _ => by decide)
  · exact_mod_cast exists_discrim_eq_of_genusCharacters isFundamentalDiscriminant_neg_twenty
      (fun _ => -1) hprod (q := 7) (by norm_num) (by rw [hD]; norm_num)
      (fun p hp hp2 => by
        rw [hD, h20] at hp
        rcases Finset.mem_insert.1 hp with rfl | hp
        · exact absurd rfl hp2
        · rw [Finset.mem_singleton.1 hp]; norm_num)
      (fun _ => by decide)

-- Problem 39 with `q = 2` at the odd discriminant `D = -15 ≡ 1 (mod 8)`: `(2/3) = (2/5) = -1`.
example : ∃ b c : ℤ, discrim (2 : ℤ) b c = -15 := by
  have h15 : (15 : ℕ).primeFactors = {3, 5} := by simp [Nat.primeFactors]
  have hD : (-15 : ℤ).natAbs = 15 := rfl
  exact_mod_cast exists_discrim_eq_of_genusCharacters isFundamentalDiscriminant_neg_fifteen
    (fun _ => -1) (by simp [hD, h15]) (q := 2) Nat.prime_two (by rw [hD]; norm_num)
    (fun p hp _ => by
      rw [hD, h15] at hp
      rcases Finset.mem_insert.1 hp with rfl | hp
      · norm_num
      · rw [Finset.mem_singleton.1 hp]; norm_num)
    (fun h => absurd h (by simp [hD, h15]))

-- The trivial genus at `D = -15`.
example : ∃ q : ℕ, q.Prime ∧ Nat.Coprime q (2 * 15) ∧
    (∀ p ∈ (15 : ℕ).primeFactors, p ≠ 2 → jacobiSym (q : ℤ) p = 1) ∧
    ∃ b c : ℤ, discrim (q : ℤ) b c = -15 := by
  obtain ⟨q, hq, hcop, hodd, -, b, c, hbc⟩ := exists_prime_genusCharacters_discrim_eq (D := -15)
    isFundamentalDiscriminant_neg_fifteen (fun _ => 1)
    (fun _ _ => Or.inl rfl) (by simp)
  exact ⟨q, hq, hcop, hodd, b, c, hbc⟩

-- The non-principal genus at `D = -20`: `(q/5) = -1` and `χ₄(q) = -1`.
example : ∃ q : ℕ, q.Prime ∧ jacobiSym (q : ℤ) 5 = -1 ∧ genusCharTwo (-20) q = -1 ∧
    ∃ b c : ℤ, discrim (q : ℤ) b c = -20 := by
  have h20 : (20 : ℕ).primeFactors = {2, 5} := by simp [Nat.primeFactors]
  obtain ⟨q, hq, -, hodd, h2, b, c, hbc⟩ := exists_prime_genusCharacters_discrim_eq (D := -20)
    isFundamentalDiscriminant_neg_twenty (fun _ => -1)
    (fun _ _ => Or.inr rfl) (by simp [h20])
  exact ⟨q, hq, hodd 5 (by simp [h20]) (by norm_num), h2 (by simp [h20]), b, c, hbc⟩

-- A positive fundamental discriminant: `D = 8 = 4·2`.
example : ∃ q : ℕ, q.Prime ∧ genusCharTwo 8 q = 1 ∧ ∃ b c : ℤ, discrim (q : ℤ) b c = 8 := by
  have h8 : (8 : ℕ).primeFactors = {2} := by simp [Nat.primeFactors]
  obtain ⟨q, hq, -, -, h2, b, c, hbc⟩ := exists_prime_genusCharacters_discrim_eq (D := 8)
    (Or.inr ⟨2, by norm_num,
      Int.squarefree_natAbs.1 (by simp [Nat.squarefree_iff_nodup_primeFactorsList]), by decide⟩)
    (fun _ => 1)
    (fun _ _ => Or.inl rfl) (by simp)
  exact ⟨q, hq, h2 (by simp [h8]), b, c, hbc⟩

end MetaMathlibExt.GenusCharacterPrimesTest
