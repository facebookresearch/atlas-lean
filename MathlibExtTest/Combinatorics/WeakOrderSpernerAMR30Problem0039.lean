/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.WeakOrderSpernerAMR30Problem0039
import Mathlib.Tactic.IntervalCases

/-! # Tests for `MathlibExt.Combinatorics.WeakOrderSpernerAMR30Problem0039` -/

namespace MathlibExtTest.WeakOrderSpernerAMR30Problem0039

open MathlibExt.Combinatorics.WeakOrderSpernerAMR30Problem0039Wanted

-- Test section: inversion sets. The identity has no inversion, so it lies below every
-- permutation in the weak order.
example (n : ℕ) : inversions (1 : Equiv.Perm (Fin n)) = ∅ :=
  Finset.filter_false_of_mem fun _ _ h => lt_asymm h.1 h.2

example (n : ℕ) (σ : Equiv.Perm (Fin n)) : weakLE 1 σ := by
  have h : inversions (1 : Equiv.Perm (Fin n)) = ∅ :=
    Finset.filter_false_of_mem fun _ _ h => lt_asymm h.1 h.2
  rw [weakLE, h]
  exact Finset.empty_subset _

-- The adjacent transposition of `Fin 2` has the single inversion `(0, 1)`, and the reversal of
-- `Fin 3` inverts all three pairs of positions.
example : inversions (Equiv.swap (0 : Fin 2) 1) = {(0, 1)} := by decide

example : (inversions (Fin.revPerm : Equiv.Perm (Fin 3))).card = 3 := by decide

-- Test section: the weak order is not total. The two adjacent transpositions of `Fin 3` are
-- incomparable, so they form an antichain with two elements.
example : IsAntichain weakLE
    (({Equiv.swap 0 1, Equiv.swap 1 2} : Finset (Equiv.Perm (Fin 3))) :
      Set (Equiv.Perm (Fin 3))) := by
  intro σ hσ τ hτ hne
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hσ hτ
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl
  · exact absurd rfl hne
  · exact fun h => absurd (h (by decide : ((0 : Fin 3), (1 : Fin 3)) ∈ inversions (Equiv.swap 0 1)))
      (by decide)
  · exact fun h => absurd (h (by decide : ((1 : Fin 3), (2 : Fin 3)) ∈ inversions (Equiv.swap 1 2)))
      (by decide)
  · exact absurd rfl hne

-- Test section: the Sperner property. In `S_3` the rank levels have sizes `1, 2, 2, 1`, so no
-- antichain has more than two elements; the antichain above shows that two is attained.
example (A : Finset (Equiv.Perm (Fin 3))) (hA : IsAntichain weakLE (A : Set (Equiv.Perm (Fin 3)))) :
    A.card ≤ 2 := by
  obtain ⟨k, hk⟩ := weakOrderSperner_holds 3 A hA
  refine hk.trans ?_
  rcases Nat.lt_or_ge k 4 with h | h
  · interval_cases k <;> decide
  · have h3 : ∀ σ : Equiv.Perm (Fin 3), (inversions σ).card ≤ 3 := by decide
    rw [Finset.card_eq_zero.2 (Finset.filter_false_of_mem fun σ _ h' => by
      have := h3 σ
      omega)]
    omega

-- Edge cases: `S_0` and `S_1` have a single permutation, so every antichain has at most one
-- element.
example (A : Finset (Equiv.Perm (Fin 0))) (hA : IsAntichain weakLE (A : Set (Equiv.Perm (Fin 0)))) :
    A.card ≤ 1 := by
  obtain ⟨k, hk⟩ := weakOrderSperner_holds 0 A hA
  exact hk.trans ((Finset.card_filter_le _ _).trans (by simp))

example (A : Finset (Equiv.Perm (Fin 1))) (hA : IsAntichain weakLE (A : Set (Equiv.Perm (Fin 1)))) :
    A.card ≤ 1 := by
  obtain ⟨k, hk⟩ := weakOrderSperner_holds 1 A hA
  exact hk.trans ((Finset.card_filter_le _ _).trans (by simp))

end MathlibExtTest.WeakOrderSpernerAMR30Problem0039
