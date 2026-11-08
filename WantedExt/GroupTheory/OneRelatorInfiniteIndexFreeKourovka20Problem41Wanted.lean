/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# One-relator groups whose infinite-index subgroups are free (Kourovka Notebook Problem 20.41)

Kourovka Notebook, Problem 20.41 (L. Ciobanu, B. Fine, G. Rosenberger), marked solved in the 21st
issue: suppose that `G` is a non-cyclic residually finite group in which every subgroup of finite
index (including the group itself) is defined by a single defining relation, while all infinite
index subgroups are free. Is it true that `G` is either free or isomorphic to the fundamental group
of a compact surface?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.ResiduallyFinite

@[expose] public section

namespace MathlibExt.GroupTheory.OneRelatorInfiniteIndexFreeKourovka20Problem41Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.41 (L. Ciobanu, B. Fine, G.
Rosenberger). UnsolvedMath record UM-00701699 (`KOU-20.41`), dataset ulamai/UnsolvedMath v1.8.0.

A group defined by a single defining relation is one isomorphic to `PresentedGroup {r}` for some `r
∈ FreeGroup (Fin n)`. Free groups are Mathlib's `IsFreeGroup`. A compact surface with boundary has a
free fundamental group, so the conclusion is: `G` is free, or `G` is isomorphic to `⟨a₁, b₁, …, a_g,
b_g | [a₁, b₁] ⋯ [a_g, b_g]⟩` for some `g`, or to `⟨c₁, …, c_k | c₁² ⋯ c_k²⟩` for some `k ≥ 1`.
Infinite index is `Subgroup.index = 0`.
-/

/-- Kourovka 20.41 (L. Ciobanu, B. Fine, G. Rosenberger): a non-cyclic residually finite group
`G` in which every subgroup of finite index (`G` included) has a presentation with finitely many
generators and one defining relation, and every subgroup of infinite index is free, is free or the
fundamental group of a closed surface: orientable of genus `g`, presented by
`⟨a₀, b₀, …, a_{g-1}, b_{g-1} | [a₀, b₀] ⋯ [a_{g-1}, b_{g-1}]⟩` (`aᵢ = (i, false)`,
`bᵢ = (i, true)`), or non-orientable of genus `k ≥ 1`, presented by
`⟨c₀, …, c_{k-1} | c₀² ⋯ c_{k-1}²⟩`. Compact surfaces with boundary have free fundamental groups. -/
def oneRelatorInfiniteIndexFreeIsFreeOrSurface : Prop :=
  ∀ (G : Type) [Group G], ¬ IsCyclic G → Group.ResiduallyFinite G →
    (∀ H : Subgroup G, H.FiniteIndex →
      ∃ (n : ℕ) (r : FreeGroup (Fin n)), Nonempty (H ≃* PresentedGroup {r})) →
    (∀ H : Subgroup G, H.index = 0 → IsFreeGroup H) →
    IsFreeGroup G ∨
      (∃ g : ℕ, Nonempty (G ≃* PresentedGroup
        {((List.finRange g).map fun i => FreeGroup.of (i, false) * FreeGroup.of (i, true) *
          (FreeGroup.of (i, false))⁻¹ * (FreeGroup.of (i, true))⁻¹).prod})) ∨
      ∃ k : ℕ, 1 ≤ k ∧ Nonempty (G ≃* PresentedGroup
        {((List.finRange k).map fun i => FreeGroup.of i ^ 2).prod})

/--
Resolved true: Wilton (Theorem D) proves that an infinite one-relator group whose subgroups of
infinite index are all free is free or the fundamental group of a closed aspherical surface; a
non-cyclic one-relator group is infinite, and the remaining hypotheses of the problem are not
needed. The 21st issue of the Kourovka Notebook marks 20.41 solved ("Yes, it is true"). Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 20.41 (L. Ciobanu, B. Fine, G. Rosenberger); resolution:
H. Wilton, Surface groups among cubulated hyperbolic and one-relator groups, preprint,
arXiv:2406.02121 (2024, v3 2026), Theorem D: an infinite one-relator group that is neither free nor
a surface group has a subgroup of infinite index that is not free (a non-cyclic one-relator group
has at least two generators and is infinite); Kourovka Notebook (21st issue), Problem 20.41: Yes, it
is true, https://arxiv.org/abs/2406.02121.
-/
public theorem_wanted oneRelatorInfiniteIndexFreeIsFreeOrSurface_holds :
    oneRelatorInfiniteIndexFreeIsFreeOrSurface

end MathlibExt.GroupTheory.OneRelatorInfiniteIndexFreeKourovka20Problem41Wanted
