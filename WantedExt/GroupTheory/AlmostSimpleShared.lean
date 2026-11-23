/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Almost simple groups

Shared definition of almost simple groups for the Kourovka Notebook entries (Problems 20.109 and
21.134(b)): a group isomorphic to a subgroup of `Aut(S)` that contains the inner automorphisms,
for a non-abelian finite simple group `S`. Moved unchanged from `Kourovka21Problem134bWanted`.
-/

module

public import Mathlib.Algebra.Group.End
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.AlmostSimpleShared

universe u

/-- **Almost simple groups.** A group $G$ is almost simple when there is a nonabelian finite simple
group $S$ such that $G$ is isomorphic to a subgroup $A$ of the automorphism group $\mathrm{Aut}(S)$
that contains the inner automorphism group $\mathrm{Inn}(S)$. -/
def IsAlmostSimple (G : Type u) [Group G] : Prop :=
  ∃ (S : Type u) (groupStructure : Group S) (finiteS : Finite S)
      (simpleS : IsSimpleGroup S),
    letI := groupStructure
    letI := finiteS
    letI := simpleS
    ¬IsMulCommutative S ∧
      ∃ A : Subgroup (MulAut S),
        MonoidHom.range (MulAut.conj : S →* MulAut S) ≤ A ∧
          Nonempty (G ≃* A)

end MathlibExt.GroupTheory.AlmostSimpleShared
