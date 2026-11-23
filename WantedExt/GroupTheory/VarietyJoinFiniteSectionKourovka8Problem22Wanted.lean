/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite groups in a join of two varieties (Kourovka Notebook Problem 8.22)

Kourovka Notebook, Archive of Solved Problems, Problem 8.22 (L. G. Kovács): if `G` is a
(non-abelian) finite group contained in a join `𝔄 ∨ 𝔅` of two varieties `𝔄`, `𝔅` of groups, must
there exist finite groups `A ∈ 𝔄`, `B ∈ 𝔅` such that `G` is a section of the direct product `A × B`?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.FormationVarietyPGroupsKourovka11Problem21Wanted
public import WantedExt.GroupTheory.NilpotentClassFourVarietyLatticeKourovka3Problem53Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.VarietyJoinFiniteSectionKourovka8Problem22Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.22 (L. G.
Kovács). UnsolvedMath record UM-00700474 (`KOU-8.22`), dataset ulamai/UnsolvedMath v1.8.0.

A variety is given by its set of laws, a fully invariant subgroup of `FreeGroup ℕ`
(`IsFullyInvariant` of Kourovka 3.53); membership is `SatisfiesLaws`
from `WantedExt/GroupTheory/FormationVarietyPGroupsKourovka11Problem21Wanted.lean`. The laws of the
join are the laws common to both varieties, `VA ⊓ VB`. A section of `X` is a quotient of a subgroup
of `X`. The parenthetical "non-abelian" is kept as a hypothesis on `G`.
-/

open MathlibExt.GroupTheory.NilpotentClassFourVarietyLatticeKourovka3Problem53Wanted
  (IsFullyInvariant)
open MathlibExt.GroupTheory.FormationVarietyPGroupsKourovka11Problem21Wanted

/-- `G` is a section of `X`: `G` is isomorphic to a quotient `K / L` of a subgroup `K` of `X`. -/
def IsSection (G X : Type*) [Group G] [Group X] : Prop :=
  ∃ (K : Subgroup X) (L : Subgroup K) (_ : L.Normal), Nonempty (K ⧸ L ≃* G)

/-- Kourovka 8.22 (L. G. Kovács): for varieties `𝔄` and `𝔅` with sets of laws `VA` and `VB` (fully
invariant subgroups of `FreeGroup ℕ`), every finite non-abelian group in the join `𝔄 ∨ 𝔅`, whose
laws are `VA ⊓ VB`, is a section of `A × B` for some finite `A ∈ 𝔄` and finite `B ∈ 𝔅`. -/
def finiteGroupInJoinIsSectionOfProduct : Prop :=
  ∀ VA VB : Subgroup (FreeGroup ℕ), IsFullyInvariant VA → IsFullyInvariant VB →
    ∀ (G : Type) [Group G] [Finite G], (∃ x y : G, x * y ≠ y * x) →
      SatisfiesLaws (VA ⊓ VB : Subgroup (FreeGroup ℕ)) G →
      ∃ (A B : Type) (_ : Group A) (_ : Group B), Finite A ∧ Finite B ∧
        SatisfiesLaws VA A ∧ SatisfiesLaws VB B ∧ IsSection G (A × B)

/--
Resolved false: the Kourovka Archive answers 8.22 "Not always", citing Storozhev (1995), who
constructs two pseudoabelian varieties `𝔐₁`, `𝔐₂` (each non-abelian, defined by one word in two
variables, with only abelian finite groups) whose join contains a finite non-abelian group `G`;
every finite `A ∈ 𝔐₁`, `B ∈ 𝔐₂` is abelian, so `G` is not a section of `A × B`. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.22 (L. G. Kovács);
resolution: A. Storozhev, On the join of varieties of groups, Bull. Austral. Math. Soc. 51 (1995),
287-290, Kourovka Archive, Problem 8.22: Not always; paper, abstract: two pseudoabelian group
varieties, each defined by one word in two variables, whose join is not pseudoabelian,
https://doi.org/10.1017/S0004972700014118.
-/
public theorem_wanted finiteGroupInJoinIsSectionOfProduct_refuted :
    ¬ finiteGroupInJoinIsSectionOfProduct

end MathlibExt.GroupTheory.VarietyJoinFiniteSectionKourovka8Problem22Wanted
