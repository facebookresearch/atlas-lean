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
# Tests for `MetaMathlibExt.exists_prime_genusCharacters`

Values of the $2$-adic genus character in each of its three cases, and the theorem at the
fundamental discriminants $-15$ (odd), $-20$ (with $\xi$) and $8$ (positive, with $\eta$).
-/

@[expose] public section

namespace MetaMathlibExt.GenusCharacterPrimesTest

#check @genusCharTwo
#check @exists_prime_genusCharacters

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

-- The trivial genus at `D = -15`.
example : ∃ q : ℕ, q.Prime ∧ Nat.Coprime q (2 * 15) ∧
    (∀ p ∈ (15 : ℕ).primeFactors, p ≠ 2 → jacobiSym (q : ℤ) p = 1) ∧
    ∃ b c : ℤ, discrim (q : ℤ) b c = -15 := by
  obtain ⟨q, hq, hcop, hodd, -, b, c, hbc⟩ := exists_prime_genusCharacters (D := -15)
    isFundamentalDiscriminant_neg_fifteen (fun _ => 1)
    (fun _ _ => Or.inl rfl) (by simp)
  exact ⟨q, hq, hcop, hodd, b, c, hbc⟩

-- The non-principal genus at `D = -20`: `(q/5) = -1` and `χ₄(q) = -1`.
example : ∃ q : ℕ, q.Prime ∧ jacobiSym (q : ℤ) 5 = -1 ∧ genusCharTwo (-20) q = -1 ∧
    ∃ b c : ℤ, discrim (q : ℤ) b c = -20 := by
  have h20 : (20 : ℕ).primeFactors = {2, 5} := by simp [Nat.primeFactors]
  obtain ⟨q, hq, -, hodd, h2, b, c, hbc⟩ := exists_prime_genusCharacters (D := -20)
    isFundamentalDiscriminant_neg_twenty (fun _ => -1)
    (fun _ _ => Or.inr rfl) (by simp [h20])
  exact ⟨q, hq, hodd 5 (by simp [h20]) (by norm_num), h2 (by simp [h20]), b, c, hbc⟩

-- A positive fundamental discriminant: `D = 8 = 4·2`.
example : ∃ q : ℕ, q.Prime ∧ genusCharTwo 8 q = 1 ∧ ∃ b c : ℤ, discrim (q : ℤ) b c = 8 := by
  have h8 : (8 : ℕ).primeFactors = {2} := by simp [Nat.primeFactors]
  obtain ⟨q, hq, -, -, h2, b, c, hbc⟩ := exists_prime_genusCharacters (D := 8)
    (Or.inr ⟨2, by norm_num,
      Int.squarefree_natAbs.1 (by simp [Nat.squarefree_iff_nodup_primeFactorsList]), by decide⟩)
    (fun _ => 1)
    (fun _ _ => Or.inl rfl) (by simp)
  exact ⟨q, hq, h2 (by simp [h8]), b, c, hbc⟩

end MetaMathlibExt.GenusCharacterPrimesTest
