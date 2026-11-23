/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Complements in compact groups with elementary Sylow subgroups (Kourovka Notebook Problem 3.58)

Kourovka Notebook, Archive of Solved Problems, Problem 3.58 (V. S. Charin): let `G` be a compact
`0`-dimensional topological group all of whose Sylow `p`-subgroups are direct products of cyclic
groups of order `p`. Then is every normal subgroup of `G` complementable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Complement
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected

@[expose] public section

namespace MathlibExt.GroupTheory.CompactGroupElementarySylowComplementKourovka3Problem58Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.58 (V. S.
Charin). UnsolvedMath record UM-00700206 (`KOU-3.58`), dataset ulamai/UnsolvedMath v1.8.0.

Compact `0`-dimensional groups are taken Hausdorff and totally disconnected (profinite). Sylow
`p`-subgroups of a profinite group are its maximal closed pro-`p` subgroups; a closed subgroup `P`
is pro-`p` when `P ∩ N` has `p`-power index in `P` for every open normal subgroup `N`. Since every
closed pro-`p` subgroup lies in a Sylow `p`-subgroup, the hypothesis is stated as: every closed
pro-`p` subgroup is abelian of exponent `p` (for a compact group, the same as a topological direct
product of cyclic groups of order `p`). In a topological group the normal subgroups in question are
the closed ones and a complement is a closed subgroup `K` with `N ∩ K = 1` and `NK = G`
(`Subgroup.IsComplement'`); a dense normal subgroup of an infinite profinite group has no closed
complement, so the question is about closed normal subgroups.
-/

/-- The subgroup `P` of the topological group `G` is a pro-`p` subgroup: its image in every
quotient `G / N` by an open normal subgroup `N` is a `p`-group, that is, `P ∩ N` has `p`-power
index in `P`. -/
def IsProPSubgroup {G : Type*} [Group G] [TopologicalSpace G] (p : ℕ) (P : Subgroup G) : Prop :=
  ∀ N : Subgroup G, IsOpen (N : Set G) → N.Normal → ∃ k : ℕ, (N.subgroupOf P).index = p ^ k

/-- Every Sylow `p`-subgroup of the profinite group `G` is a direct product of cyclic groups of
order `p`, for every prime `p`: every closed pro-`p` subgroup (each lies in a Sylow `p`-subgroup,
a maximal one) is abelian of exponent `p`, which for a compact group is the same as being a
topological direct product of cyclic groups of order `p`. -/
def HasElementaryAbelianSylowSubgroups (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ p : ℕ, p.Prime → ∀ P : Subgroup G, IsClosed (P : Set G) → IsProPSubgroup p P →
    (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧ ∀ x ∈ P, x ^ p = 1

/-- Kourovka 3.58 (V. S. Charin): in a compact `0`-dimensional (Hausdorff, totally disconnected)
group all of whose Sylow `p`-subgroups are direct products of cyclic groups of order `p`, every
closed normal subgroup has a closed complement. -/
def compactElementarySylowNormalComplemented : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G], HasElementaryAbelianSylowSubgroups G →
    ∀ N : Subgroup G, IsClosed (N : Set G) → N.Normal →
      ∃ K : Subgroup G, IsClosed (K : Set G) ∧ N.IsComplement' K

/--
Resolved true: Kabenyuk proves that in a compact `0`-dimensional group whose Sylow `p`-subgroups are
direct products of cyclic groups of order `p` every normal subgroup is complementable; the Kourovka
Archive answers 3.58 "Yes, it is". Normal subgroups and complements are taken closed. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.58 (V. S. Charin);
resolution: M. I. Kabenyuk, On the complementability of subgroups in compact groups, Siberian Math.
J. 13 (1972), 654-657, Kourovka Archive of Solved Problems, Problem 3.58: Yes, it is,
https://doi.org/10.1007/BF00971059.
-/
public theorem_wanted compactElementarySylowNormalComplemented_holds :
    compactElementarySylowNormalComplemented

end MathlibExt.GroupTheory.CompactGroupElementarySylowComplementKourovka3Problem58Wanted
