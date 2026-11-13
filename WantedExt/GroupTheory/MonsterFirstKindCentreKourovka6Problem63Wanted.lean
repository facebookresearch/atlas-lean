/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Monsters of the first kind with finite proper subgroups (Kourovka Notebook Problem 6.63)

Kourovka Notebook, Archive of Solved Problems, Problem 6.63 (V. P. Shunkov): an infinite group G is
a monster of the first kind if it has elements of order > 2 and for any such element a and any
proper subgroup H there is g ∈ G \ H with ⟨a, aᵍ⟩ = G. Classify the monsters of the first kind all
of whose proper subgroups are finite.
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.MonsterTorsionFreeCentralExtensionKourovka14Problem104Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.MonsterFirstKindCentreKourovka6Problem63Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.63 (V. P.
Shunkov). UnsolvedMath record UM-00700405 (`KOU-6.63`), dataset ulamai/UnsolvedMath v1.8.0.

Monsters of the first kind are `IsMonsterFirstKind` of the Kourovka 14.104 module (infinite order
counts as order greater than `2`). The target is the characterization in the Archive's answer: among
infinite groups whose proper subgroups are finite, the monsters of the first kind are those whose
centre is the set `{g | g² = 1}` of elements of order at most `2`.
-/

open MathlibExt.GroupTheory.MonsterTorsionFreeCentralExtensionKourovka14Problem104Wanted
  (IsMonsterFirstKind)

/-- Kourovka 6.63 (V. P. Shunkov), the Archive's characterization: an infinite group all of whose
proper subgroups are finite is a monster of the first kind exactly when its centre is the set of
elements of order at most `2`. -/
def monsterFirstKindCharacterization : Prop :=
  ∀ (G : Type) [Group G], Infinite G → (∀ H : Subgroup G, H ≠ ⊤ → (H : Set G).Finite) →
    (IsMonsterFirstKind G ↔ (Subgroup.center G : Set G) = {g : G | g ^ 2 = 1})

/--
Resolved true: the Kourovka Archive answers 6.63 with the characterization of Shunkov (1970, one
direction) and Sozutov (1997, the converse): an infinite group all of whose proper subgroups are
finite is a monster of the first kind exactly when its centre is the set of elements of order at
most `2`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.63
(V. P. Shunkov); resolution: V. P. Shunkov, A periodic group with almost regular involutions,
Algebra and Logic 7 (1968), 66-69 (1970); A. I. Sozutov, The existence of f-local subgroups in a
group, Algebra and Logic 36, no. 5 (1997), 336-348, Kourovka Archive, Problem 6.63: the centre of
such a group coincides with the set of elements of order ≤ 2 (Shunkov); an infinite group all of
whose proper subgroups are finite is a monster of the first kind if its centre coincides with the
set of elements of order ≤ 2 (Sozutov); there are continuously many such groups (Olshanskii),
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted monsterFirstKindCharacterization_holds : monsterFirstKindCharacterization

end MathlibExt.GroupTheory.MonsterFirstKindCentreKourovka6Problem63Wanted
