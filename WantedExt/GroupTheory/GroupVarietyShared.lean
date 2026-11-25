/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Varieties of groups through their laws (Kourovka Notebook Problems 6.14-6.17)

Shared definitions for the problems on varieties of groups: a variety is represented by its set of
laws, a fully invariant subgroup `N` of the free group `FreeGroup ℕ` on countably many letters
(`IsFullyInvariant` of Kourovka 3.53; the groups of the variety are those satisfying every
word of `N`, see `SatisfiesLaws`). This is a
bijection between varieties and fully invariant subgroups that reverses inclusion:
`V(N') ⊆ V(N)` exactly when `N ≤ N'`, the join of two varieties has laws `N ⊓ N'`, and their meet
has laws `N ⊔ N'`.
-/

module

public import Mathlib.GroupTheory.Finiteness
public import WantedExt.GroupTheory.FormationVarietyPGroupsKourovka11Problem21Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.GroupVarietyShared

open MathlibExt.GroupTheory.FormationVarietyPGroupsKourovka11Problem21Wanted (SatisfiesLaws)

/-- **Locally finite variety.** Let $F$ be the free group on countably many generators
$x_0, x_1, x_2, \dots$ and let $N$ be a subgroup of $F$, regarded as a set of laws. The variety
defined by $N$ is locally finite if every finitely generated group satisfying all laws in $N$ is
finite. -/
def IsLocallyFiniteVariety (N : Subgroup (FreeGroup ℕ)) : Prop :=
  ∀ (G : Type) [Group G], SatisfiesLaws (N : Set (FreeGroup ℕ)) G → Group.FG G → Finite G

end MathlibExt.GroupTheory.GroupVarietyShared
