/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Normal subgroups of R̃N-groups (Kourovka Notebook Problem 8.17)

Kourovka Notebook, Archive of Solved Problems, Problem 8.17 (Sh. S. Kemkhadze): an `R̃N`-group is
one whose every homomorphic image is an `RN`-group. Is the class of `R̃N`-groups closed under taking
normal subgroups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import WantedExt.GroupTheory.NZeroGroupNTildeGroupKourovka1Problem38Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.RNTildeGroupNormalSubgroupKourovka8Problem17Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.17 (Sh. S.
Kemkhadze). UnsolvedMath record UM-00700469 (`KOU-8.17`), dataset ulamai/UnsolvedMath v1.8.0.

`RN` is the Kurosh-Chernikov class of groups with a solvable normal system: a normal system (a
complete chain of subgroups in which the lower member of every jump is normal in the upper one;
`IsNormalSystem` from `WantedExt/GroupTheory/NZeroGroupNTildeGroupKourovka1Problem38Wanted.lean`)
all of whose factors are abelian. This is an implicit convention: the Notebook keeps the Russian
Kurosh-Chernikov name `RN`, and the English translation of Kurosh, The Theory of Groups, vol. II,
§56 (normal systems) and §58 ("A group G is called an SN-group if it has a solvable normal system"),
calls the same class `SN`, the S-notation of the cited paper of Wilson (`S̄I`) and of his own
Notebook problem (`S̄I`, `S̄N`). Homomorphic images are the quotients `G / N`.
-/

open MathlibExt.GroupTheory.NZeroGroupNTildeGroupKourovka1Problem38Wanted

/-- `G` is an `RN`-group (Kurosh and Chernikov; `SN`-group in later notation): `G` has a normal
system all of whose factors `B / A` (jumps `A < B`) are abelian. -/
def IsRNGroup (G : Type) [Group G] : Prop :=
  ∃ S : Set (Subgroup G), IsNormalSystem S ∧ ∀ A ∈ S, ∀ B ∈ S, A < B →
    (∀ C ∈ S, ¬ (A < C ∧ C < B)) → ∀ x ∈ B, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ A

/-- `G` is an `R̃N`-group: every homomorphic image of `G` is an `RN`-group. -/
def IsRNTildeGroup (G : Type) [Group G] : Prop :=
  ∀ (N : Subgroup G) (_ : N.Normal), IsRNGroup (G ⧸ N)

/-- Kourovka 8.17 (Sh. S. Kemkhadze): the class of `R̃N`-groups is closed under taking normal
subgroups. -/
def rnTildeClosedUnderNormalSubgroups : Prop :=
  ∀ (G : Type) [Group G], IsRNTildeGroup G → ∀ N : Subgroup G, N.Normal → IsRNTildeGroup N

/--
Resolved false: the Kourovka Archive answers 8.17 "No", citing Wilson, On normal subgroups of
`S̄I`-groups (1974). Wilson's Theorem (§1, p. 574) gives a group `G` with a normal subgroup `H`, `G
/ H` infinite cyclic, such that every proper quotient of `G` is nilpotent-by-cyclic and `G` is an
`S̄I`-group (all chief factors abelian), while `H` maps onto a non-abelian simple group. So every
homomorphic image of `G` has a normal system with abelian factors, and `H` has a non-abelian simple
image, which has none. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 8.17 (Sh. S. Kemkhadze); resolution: J. S. Wilson, On normal subgroups of SI-bar-groups,
Arch. Math. 25 (1974), 574-577, Kourovka Archive, Problem 8.17: No (Wilson); paper, §1 Theorem (p.
574), https://doi.org/10.1007/BF01238728.
-/
public theorem_wanted rnTildeClosedUnderNormalSubgroups_refuted :
    ¬ rnTildeClosedUnderNormalSubgroups

end MathlibExt.GroupTheory.RNTildeGroupNormalSubgroupKourovka8Problem17Wanted
