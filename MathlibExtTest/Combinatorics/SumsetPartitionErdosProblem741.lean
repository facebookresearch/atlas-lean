/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SumsetPartitionErdosProblem741

/-!
# Tests for the bounded-gap obstruction

A basis with the obstruction has a part with unbounded sumset gaps in every complementary
partition, including the partition into even and odd elements.
-/

namespace MathlibExtTest.Combinatorics.SumsetPartitionErdosProblem741

open MathlibExt.Combinatorics.SumsetPartitionErdosProblem741Wanted
open scoped Pointwise

example : ∃ A : Set ℕ, A.IsAsymptoticAddBasisOfOrder 2 ∧
    ∀ B : Set ℕ, B ⊆ A →
      ¬ HasBoundedGaps (B + B) ∨ ¬ HasBoundedGaps ((A \ B) + (A \ B)) := by
  obtain ⟨A, hA, hsplit⟩ := basisWithoutBoundedGapSplit_holds
  refine ⟨A, hA, fun B hB ↦ ?_⟩
  exact not_and_or.mp (hsplit B (A \ B) Set.disjoint_sdiff_right
    (Set.union_sdiff_cancel hB))

example : ∃ A : Set ℕ, A.IsAsymptoticAddBasisOfOrder 2 ∧
    ¬ (HasBoundedGaps ((A ∩ {n | Even n}) + (A ∩ {n | Even n})) ∧
      HasBoundedGaps ((A \ {n | Even n}) + (A \ {n | Even n}))) := by
  obtain ⟨A, hA, hsplit⟩ := basisWithoutBoundedGapSplit_holds
  refine ⟨A, hA, hsplit _ _ ?_ ?_⟩
  · exact Set.disjoint_sdiff_right.mono_left Set.inter_subset_right
  · exact Set.inter_union_sdiff A {n | Even n}

end MathlibExtTest.Combinatorics.SumsetPartitionErdosProblem741
