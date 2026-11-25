/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.IsomorphicNormalSubgroupsKourovka12Problem45

/-! # Tests for Hall's question on isomorphic normal subgroups -/

namespace MathlibExtTest.GroupTheory.IsomorphicNormalSubgroupsKourovka12Problem45

open MathlibExt.GroupTheory.IsomorphicNormalSubgroupsKourovka12Problem45Wanted

-- Extract a group with a proper nontrivial normal copy of itself from the refutation.
example : ∃ (G : Type) (_ : Group G) (N : Subgroup G),
    N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ ∧ Nonempty (N ≃* G) := by
  by_contra h
  apply isoToNormalSubgroupsFreeSimpleOrCyclic_refuted
  intro G _ hG hiso
  right
  left
  refine ⟨fun N hn => ?_⟩
  by_cases hb : N = ⊥
  · exact Or.inl hb
  · exact Or.inr (by_contra fun ht => h ⟨G, inferInstance, N, hn, hb, ht, hiso N hn hb⟩)

end MathlibExtTest.GroupTheory.IsomorphicNormalSubgroupsKourovka12Problem45
