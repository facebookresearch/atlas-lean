/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.IdentityProductNecklace
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic

/-! # Tests for the least-period partition of identity-product tuples -/

open MetaMathlibExt

-- The empty tuple has product one and least positive period one.
example (G : Type*) [Group G] [Fintype G] :
    (∑ d ∈ (4 : ℕ).divisors, Set.ncard {x : Fin 0 → G | (List.ofFn x).prod = 1 ∧
      x ∘ ⇑((finRotate 0) ^ d) = x ∧ ∀ l, 0 < l → l < d → x ∘ ⇑((finRotate 0) ^ l) ≠ x}) =
      1 := by
  rw [← card_identityProduct_period_eq_sum_smallestPeriod G 0 4 (by decide)]
  refine Set.ncard_eq_one.mpr ⟨fun i => i.elim0, ?_⟩
  ext x
  have hprod : (List.ofFn x).prod = 1 := by simp
  exact iff_of_true ⟨hprod, Subsingleton.elim _ _⟩ (Subsingleton.elim _ _)

-- For k = 1, there are no smaller positive periods to exclude.
example (G : Type*) [Group G] [Fintype G] (n : ℕ) :
    Set.ncard {x : Fin n → G | (List.ofFn x).prod = 1 ∧ x ∘ finRotate n = x} =
      Set.ncard {x : Fin n → G | (List.ofFn x).prod = 1 ∧
        x ∘ finRotate n = x ∧ ∀ l, 0 < l → l < 1 → x ∘ ⇑((finRotate n) ^ l) ≠ x} := by
  simpa only [Nat.divisors_one, Finset.sum_singleton, pow_one] using
    card_identityProduct_period_eq_sum_smallestPeriod G n 1 (hk := Nat.one_pos)

private abbrev C₃ := Multiplicative (ZMod 3)

-- Six does not divide two. In C₃ the three identity-product pairs are all fixed by six
-- rotations: one pair has least period one and the other two have least period two.
example : (∑ d ∈ (6 : ℕ).divisors, Set.ncard {x : Fin 2 → C₃ | (List.ofFn x).prod = 1 ∧
    x ∘ ⇑((finRotate 2) ^ d) = x ∧ ∀ l, 0 < l → l < d → x ∘ ⇑((finRotate 2) ^ l) ≠ x}) =
    3 := by
  rw [← card_identityProduct_period_eq_sum_smallestPeriod C₃ 2 6 (by decide)]
  let inst : Fintype {x : Fin 2 → C₃ // (List.ofFn x).prod = 1 ∧
      x ∘ ⇑((finRotate 2) ^ 6) = x} := Subtype.fintype _
  rw [Set.ncard_eq_toFinset_card']
  decide
