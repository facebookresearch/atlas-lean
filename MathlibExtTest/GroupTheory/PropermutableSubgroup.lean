/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.PropermutableSubgroup

namespace MathlibExt.GroupTheory.PropermutableSubgroupKourovka18Problem91Wanted.Tests

-- For a normal subgroup, the trivial supplement suffices.
private theorem normal_propermutable {G : Type} [Group G] (H : Subgroup G) [H.Normal] :
    IsPropermutable H := by
  refine ⟨⊥, ?_, fun X hX ↦ ?_⟩
  · simp [Subgroup.normalizer_eq_top]
  · rw [le_bot_iff.mp hX]
    simp [Permutes]

-- Normality in the ambient group still gives propermutability after restriction.
example {G : Type} [Group G] (A B : Subgroup G) [A.Normal] :
    IsPropermutable (A.subgroupOf B) :=
  normal_propermutable _

-- The counterexample thus also witnesses failure of normality inside the intermediate group.
example : ∃ (G : Type) (_ : Group G) (_ : Finite G) (A B : Subgroup G),
    A ≤ B ∧ IsPropermutable A ∧ ¬ (A.subgroupOf B).Normal := by
  obtain ⟨G, _, _, A, B, hAB, hA, hB⟩ := propermutableNotInIntermediate_holds
  exact ⟨G, ‹Group G›, ‹Finite G›, A, B, hAB, hA, fun _ ↦ hB (normal_propermutable _)⟩

end MathlibExt.GroupTheory.PropermutableSubgroupKourovka18Problem91Wanted.Tests
