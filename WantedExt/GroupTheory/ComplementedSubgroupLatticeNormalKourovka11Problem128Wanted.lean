/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Normal subgroups of K-groups (Kourovka Notebook Problem 11.128)

Kourovka Notebook, Archive of Solved Problems, Problem 11.128 (M. Emaldi): a group `G` is a
`K`-group if every subgroup `A` has a subgroup `B` with `A ∩ B = 1` and `⟨A, B⟩ = G`. Are normal
subgroups of `K`-groups also `K`-groups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.ComplementedSubgroupLatticeNormalKourovka11Problem128Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.128 (M.
Emaldi). UnsolvedMath record UM-00700820 (`KOU-11.128`), dataset ulamai/UnsolvedMath v1.8.0.

`A ∩ B = 1` and `⟨A, B⟩ = G` are `A ⊓ B = ⊥` and `A ⊔ B = ⊤` in the subgroup lattice, that is
`IsCompl A B`, so a `K`-group is a group whose subgroup lattice is complemented: Mathlib's
`ComplementedLattice (Subgroup G)`. Groups are in `Type`.
-/

/-- Kourovka 11.128 (M. Emaldi): every normal subgroup of a `K`-group is a `K`-group, a `K`-group
being a group whose subgroup lattice is complemented (`ComplementedLattice`). -/
def normalSubgroupOfKGroupIsKGroup : Prop :=
  ∀ (G : Type) [Group G], ComplementedLattice (Subgroup G) → ∀ N : Subgroup G, N.Normal →
    ComplementedLattice (Subgroup N)

/--
Resolved false: the Kourovka Archive answers 11.128 "No, it is not" (Obraztsov): some `K`-group has
a normal subgroup that is not a `K`-group. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 11.128 (M. Emaldi); resolution: V. N. Obraztsov, J. Austral. Math. Soc.
(Ser. A) 61, no. 2 (1996), 267-288, Kourovka Archive, Problem 11.128: "No, it is not",
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted normalSubgroupOfKGroupIsKGroup_refuted : ¬ normalSubgroupOfKGroupIsKGroup

end MathlibExt.GroupTheory.ComplementedSubgroupLatticeNormalKourovka11Problem128Wanted
