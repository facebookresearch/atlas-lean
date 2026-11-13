/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Groups with complemented infinite abelian subgroups (Kourovka Notebook Problem 5.62)

Kourovka Notebook, Archive of Solved Problems, Problem 5.62 (S. N. Chernikov): is a group locally
finite if it contains infinite abelian subgroups and all of them are complementable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Complement
public import WantedExt.GroupTheory.LocallyFiniteSimpleFiniteRankKourovka1Problem23Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.ComplementedInfiniteAbelianSubgroupsKourovka5Problem62Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.62 (S. N.
Chernikov). UnsolvedMath record UM-00700341 (`KOU-5.62`), dataset ulamai/UnsolvedMath v1.8.0.

A subgroup `A` is complementable when some subgroup `K` satisfies `A ∩ K = 1` and `A K = G`
(Mathlib's `Subgroup.IsComplement'`); 'all of them' refers to the infinite abelian subgroups.
Locally finite is `IsLocallyFinite` of the Kourovka 1.23 module.
-/

open MathlibExt.GroupTheory.LocallyFiniteSimpleFiniteRankKourovka1Problem23Wanted (IsLocallyFinite)

/-- Kourovka 5.62 (S. N. Chernikov): a group that has infinite abelian subgroups, all of which are
complemented (`A ∩ K = 1`, `A K = G` for some subgroup `K`), is locally finite. -/
def complementedInfiniteAbelianLocallyFinite : Prop :=
  ∀ (G : Type) [Group G],
    (∃ A : Subgroup G, (A : Set G).Infinite ∧ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
    (∀ A : Subgroup G, (A : Set G).Infinite → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      ∃ K : Subgroup G, A.IsComplement' K) →
    IsLocallyFinite G

/--
Resolved false: the Kourovka Archive answers 5.62 "Not always", citing N. S. Chernikov (1980): some
group that has infinite abelian subgroups, all of them complemented, is not locally finite. Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.62 (S. N. Chernikov);
resolution: N. S. Chernikov, Groups with complemented infinite Abelian subgroups, Math. Notes 28
(1980), 788-792 (Mat. Zametki 28 (1980), 665-674), Kourovka Archive, Problem 5.62: Not always (N. S.
Chernikov), https://doi.org/10.1007/BF01141082.
-/
public theorem_wanted complementedInfiniteAbelianLocallyFinite_refuted :
    ¬ complementedInfiniteAbelianLocallyFinite

end MathlibExt.GroupTheory.ComplementedInfiniteAbelianSubgroupsKourovka5Problem62Wanted
