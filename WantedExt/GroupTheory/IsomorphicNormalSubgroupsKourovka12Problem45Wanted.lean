/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Groups isomorphic to all their nontrivial normal subgroups (Kourovka Notebook Problem 12.45)

Kourovka Notebook, Archive of Solved Problems, Problem 12.45 (P. Hall; J. C. Lennox): must a
non-trivial group which is isomorphic to each of its non-trivial normal subgroups be free of
infinite rank, simple, or infinite cyclic?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.IsomorphicNormalSubgroupsKourovka12Problem45Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.45 (P. Hall;
J. C. Lennox). UnsolvedMath record UM-00700864 (`KOU-12.45`), dataset ulamai/UnsolvedMath v1.8.0.

Free of infinite rank means isomorphic to the free group on an infinite type; simple is
`IsSimpleGroup`; infinite cyclic is cyclic and infinite. The isomorphisms with the normal subgroups
are abstract.
-/

/-- Kourovka 12.45 (P. Hall): a nontrivial group that is isomorphic to each of its nontrivial
normal subgroups is free of infinite rank, simple, or infinite cyclic. -/
def isoToNormalSubgroupsFreeSimpleOrCyclic : Prop :=
  ∀ (G : Type) [Group G], Nontrivial G →
    (∀ N : Subgroup G, N.Normal → N ≠ ⊥ → Nonempty (N ≃* G)) →
    (∃ X : Type, Infinite X ∧ Nonempty (FreeGroup X ≃* G)) ∨ IsSimpleGroup G ∨
      (IsCyclic G ∧ Infinite G)

/--
Resolved false: the Kourovka Archive answers 12.45 No (V. N. Obraztsov, 1997): some nontrivial group
isomorphic to each of its nontrivial normal subgroups is neither free of infinite rank, nor simple,
nor infinite cyclic. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 12.45 (P. Hall; J. C. Lennox); resolution: V. N. Obraztsov, Proc. London Math. Soc. (3) 75
(1997), 79-98, Kourovka Archive, Problem 12.45: No.
-/
public theorem_wanted isoToNormalSubgroupsFreeSimpleOrCyclic_refuted :
    ¬ isoToNormalSubgroupsFreeSimpleOrCyclic

end MathlibExt.GroupTheory.IsomorphicNormalSubgroupsKourovka12Problem45Wanted
