/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.PermutingConjugatesSimpleGroupKourovka10Problem66
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Tests for the refutation of Kourovka Problem 10.66 -/

namespace MathlibExtTest.GroupTheory.PermutingConjugatesSimpleGroupKourovka10Problem66

open MathlibExt.GroupTheory.PermutingConjugatesSimpleGroupKourovka10Problem66Wanted
open scoped Pointwise

example : ¬ permutingConjugatesNotSimple := permutingConjugatesNotSimple_refuted

-- The refutation provides a simple group with two nontrivial subgroups whose product set is not
-- the whole group and such that the first permutes with every conjugate of the second. In such a
-- group the second subgroup is proper and not normal.
example : ∃ (G : Type) (_ : Group G) (A B : Subgroup G), IsSimpleGroup G ∧ A ≠ ⊥ ∧ B ≠ ⊥ ∧
    B ≠ ⊤ ∧ ¬ B.Normal ∧ (A : Set G) * (B : Set G) ≠ Set.univ ∧
    ∀ g : G, (A : Set G) * (B.map (MulAut.conj g).toMonoidHom : Set G) =
      (B.map (MulAut.conj g).toMonoidHom : Set G) * (A : Set G) := by
  by_contra hne
  apply permutingConjugatesNotSimple_refuted
  intro G _ A B hA hB hAB hperm hs
  have htop : B ≠ ⊤ := by
    rintro rfl
    exact hAB (Set.eq_univ_of_forall fun x =>
      Set.mem_mul.mpr ⟨1, A.one_mem, x, Subgroup.mem_top x, one_mul x⟩)
  have hnormal : ¬ B.Normal := by
    intro hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B with h | h
    · exact hB h
    · exact htop h
  exact hne ⟨G, inferInstance, A, B, hs, hA, hB, htop, hnormal, hAB, hperm⟩

-- In a group of prime order a nontrivial subgroup is the whole group, so the hypotheses of the
-- conjecture can never hold there: the product set is always the whole group.
example {G : Type} [Group G] [Fact (Nat.card G).Prime] (A B : Subgroup G) (hA : A ≠ ⊥) :
    (A : Set G) * (B : Set G) = Set.univ := by
  rcases A.eq_bot_or_eq_top_of_prime_card with h | rfl
  · exact absurd h hA
  · exact Set.eq_univ_of_forall fun x =>
      Set.mem_mul.mpr ⟨x, Subgroup.mem_top x, 1, B.one_mem, mul_one x⟩

end MathlibExtTest.GroupTheory.PermutingConjugatesSimpleGroupKourovka10Problem66
