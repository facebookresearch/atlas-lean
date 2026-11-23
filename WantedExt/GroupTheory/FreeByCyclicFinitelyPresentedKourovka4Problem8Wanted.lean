/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finitely generated free-by-cyclic groups are finitely presented (Kourovka Notebook Problem 4.8)

Kourovka Notebook, Archive of Solved Problems, Problem 4.8 (G. Baumslag): suppose G is a finitely
generated free-by-cyclic group; is G finitely presented?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

@[expose] public section

namespace MathlibExt.GroupTheory.FreeByCyclicFinitelyPresentedKourovka4Problem8Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.8 (G.
Baumslag). UnsolvedMath record UM-00700219 (`KOU-4.8`), dataset ulamai/UnsolvedMath v1.8.0.

Free-by-cyclic: `G` has a normal subgroup `N` that is a free group (of any rank) with `G / N` cyclic
(finite or infinite). Finitely presented is Mathlib's `Group.IsFinitelyPresented`. The target also
states the Archive's stronger answer that every finitely generated subgroup is finitely presented.
-/

/-- Kourovka 4.8 (G. Baumslag): a finitely generated free-by-cyclic group `G` (with a free normal
subgroup `N` and `G / N` cyclic) is finitely presented; moreover every finitely generated subgroup
of `G` is finitely presented. -/
def freeByCyclicFinitelyPresented : Prop :=
  ∀ (G : Type) [Group G] [Group.FG G] (N : Subgroup G) [N.Normal], IsFreeGroup N →
    IsCyclic (G ⧸ N) →
      Group.IsFinitelyPresented G ∧ ∀ H : Subgroup G, Group.FG H → Group.IsFinitelyPresented H

/--
Resolved true: the Kourovka Archive answers 4.8 "Yes, it is; moreover, every finitely generated
subgroup is finitely presented", by Feighn and Handel for infinite cyclic extensions (finitely
generated subgroups of mapping tori of injective free group endomorphisms are finitely presented,
Ann. of Math. 149 (1999), abstract) and an easier argument for finite cyclic extensions. Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.8 (G. Baumslag); resolution:
M. Feighn and M. Handel, Mapping tori of free group automorphisms are coherent, Ann. of Math. 149
(1999), 1061-1077, arXiv:math/9905209, abstract: a mapping torus of an injective free group
endomorphism has the property that its finitely generated subgroups are finitely presented; Kourovka
Archive, Problem 4.8: Yes, it is; moreover, every finitely generated subgroup is finitely presented
(Feighn-Handel for infinite cyclic extensions; an easier argument for finite cyclic ones),
https://arxiv.org/abs/math/9905209.
-/
public theorem_wanted freeByCyclicFinitelyPresented_holds : freeByCyclicFinitelyPresented

end MathlibExt.GroupTheory.FreeByCyclicFinitelyPresentedKourovka4Problem8Wanted
