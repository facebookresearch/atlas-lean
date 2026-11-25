/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Poset.OrderPolynomialReciprocity

open MathlibExt.Combinatorics.Poset.OrderPolynomial
open MathlibExt.Combinatorics.Poset.OrderPolynomialWanted

namespace MathlibExtTest.Combinatorics.Poset.OrderPolynomialReciprocity

-- There is one empty map, even when the target chain is empty.
example : ∃ Q : Polynomial ℚ, Q.eval 0 = 1 := by
  obtain ⟨Q, _, hstrict⟩ := orderPolynomial_reciprocity (Fin 0)
  have h : strictOrderPolynomialValue (Fin 0) 0 = 1 := by
    rw [strictOrderPolynomialValue, Nat.card_eq_fintype_card]
    rfl
  exact ⟨Q, by simpa [h] using hstrict 0⟩

-- The two-element chain has six weak maps and three strict maps to the three-element chain.
example : ∃ Q : Polynomial ℚ, Q.eval 3 = 6 ∧ Q.eval (-3) = 3 := by
  obtain ⟨Q, hweak, hstrict⟩ := orderPolynomial_reciprocity (Fin 2)
  have hw : orderPolynomialValue (Fin 2) 3 = 6 := by
    rw [orderPolynomialValue, Nat.card_eq_fintype_card]
    rfl
  have hs : strictOrderPolynomialValue (Fin 2) 3 = 3 := by
    rw [strictOrderPolynomialValue, Nat.card_eq_fintype_card]
    rfl
  refine ⟨Q, by simpa [hw] using hweak 3, ?_⟩
  simpa [hs] using hstrict 3

-- Two incomparable minima can both map to zero below their common upper bound.
private abbrev Fork := {p : Fin 2 × Fin 2 // p ≠ (0, 0)}

example : ∃ Q : Polynomial ℚ, Q.eval 2 = 5 ∧ Q.eval (-2) = -1 := by
  obtain ⟨Q, hweak, hstrict⟩ := orderPolynomial_reciprocity Fork
  have hc : Fintype.card Fork = 3 := rfl
  have hw : orderPolynomialValue Fork 2 = 5 := by
    rw [orderPolynomialValue, Nat.card_eq_fintype_card]
    rfl
  have hs : strictOrderPolynomialValue Fork 2 = 1 := by
    let (a b : Fork) : Decidable (a < b) :=
      decidable_of_iff (a ≤ b ∧ ¬b ≤ a) lt_iff_le_not_ge.symm
    rw [strictOrderPolynomialValue, Nat.card_eq_fintype_card]
    rfl
  refine ⟨Q, by simpa [hw] using hweak 2, ?_⟩
  have he := hstrict 2
  norm_num [hc, hs] at he
  linarith

end MathlibExtTest.Combinatorics.Poset.OrderPolynomialReciprocity
