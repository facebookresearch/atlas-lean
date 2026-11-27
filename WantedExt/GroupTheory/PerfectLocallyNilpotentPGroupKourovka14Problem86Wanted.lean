/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Perfect locally nilpotent `p`-groups (Kourovka Notebook Problem 14.86)

Kourovka Notebook, Archive of Solved Problems, Problem 14.86 (J. Wiegold): does there exist an
infinite locally nilpotent `p`-group that is equal to its commutator subgroup and in which every
proper subgroup is nilpotent?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.PerfectLocallyNilpotentPGroupKourovka14Problem86Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.86 (J.
Wiegold). UnsolvedMath record UM-00701071 (`KOU-14.86`), dataset ulamai/UnsolvedMath v1.8.0.

Locally nilpotent means that every finitely generated subgroup is nilpotent, and a `p`-group is a
group all of whose elements have `p`-power order (`IsPGroup`). The target asks for such a group for
some prime `p`, so its refutation covers every prime. Groups are taken in `Type`.
-/

/-- A group is locally nilpotent if every finitely generated subgroup is nilpotent. -/
def IsLocallyNilpotent (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, H.FG → Group.IsNilpotent H

/-- **Kourovka 14.86: perfect locally nilpotent $p$-groups with nilpotent proper subgroups.** The
proposition that for some prime $p$ there is an infinite locally nilpotent $p$-group $G$ (every
element of $G$ has order a power of $p$) such that $G = [G, G]$ and every proper subgroup of $G$
is nilpotent. -/
def perfectLocallyNilpotentPGroupWithNilpotentProperSubgroups : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∃ (G : Type) (_ : Group G), Infinite G ∧ IsPGroup p G ∧
    IsLocallyNilpotent G ∧ commutator G = ⊤ ∧ ∀ H : Subgroup G, H ≠ ⊤ → Group.IsNilpotent H

/--
**No infinite perfect locally nilpotent $p$-group has only nilpotent proper subgroups.** There is
no prime $p$ and no infinite locally nilpotent $p$-group $G$ (every element of $G$ has order a
power of $p$) such that $G = [G, G]$ and every proper subgroup of $G$ is nilpotent.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.86
(J. Wiegold); resolution: A. O. Asar, Locally nilpotent p-groups whose proper subgroups are
hypercentral or nilpotent-by-Chernikov, J. London Math. Soc. (2) 61 (2000), no. 2, 412-422, Kourovka
Archive, Problem 14.86 (answer: No, it does not exist).
-/
public theorem_wanted perfectLocallyNilpotentPGroupWithNilpotentProperSubgroups_refuted :
    ¬ perfectLocallyNilpotentPGroupWithNilpotentProperSubgroups

end MathlibExt.GroupTheory.PerfectLocallyNilpotentPGroupKourovka14Problem86Wanted
