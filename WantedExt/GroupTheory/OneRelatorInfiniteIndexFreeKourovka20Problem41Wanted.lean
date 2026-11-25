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

/-- **Kourovka Problem 20.41: one-relator groups with free infinite-index subgroups.** The
proposition that every non-cyclic residually finite group $G$ such that every subgroup of finite
index in $G$ (including $G$ itself) is isomorphic to a one-relator group
$\langle x_0, \dots, x_{n-1} \mid r \rangle$ for some natural number $n$ and some element $r$ of
the free group on $x_0, \dots, x_{n-1}$, and every subgroup of infinite index in $G$ is free, is
free, or is isomorphic to
$\langle a_0, b_0, \dots, a_{g-1}, b_{g-1} \mid [a_0, b_0] \cdots [a_{g-1}, b_{g-1}] \rangle$ for
some $g \ge 0$, where $[a, b] = a b a^{-1} b^{-1}$, or is isomorphic to
$\langle c_0, \dots, c_{k-1} \mid c_0^2 \cdots c_{k-1}^2 \rangle$ for some $k \ge 1$. The problem is
due to L. Ciobanu, B. Fine and G. Rosenberger.

These presentations are the fundamental groups of the closed orientable surface of genus $g$ and
the closed non-orientable surface of genus $k$; compact surfaces with boundary have free
fundamental groups. -/
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
**Kourovka Problem 20.41 has a positive answer.** Let $G$ be a non-cyclic residually finite group
such that every subgroup of finite index in $G$ (including $G$ itself) is isomorphic to a
one-relator group $\langle x_0, \dots, x_{n-1} \mid r \rangle$ for some natural number $n$ and
some element $r$ of the free group on $x_0, \dots, x_{n-1}$, and every subgroup of infinite index
in $G$ is free. Then $G$ is free, or $G$ is isomorphic to
$\langle a_0, b_0, \dots, a_{g-1}, b_{g-1} \mid [a_0, b_0] \cdots [a_{g-1}, b_{g-1}] \rangle$ for
some $g \ge 0$, where $[a, b] = a b a^{-1} b^{-1}$, or $G$ is isomorphic to
$\langle c_0, \dots, c_{k-1} \mid c_0^2 \cdots c_{k-1}^2 \rangle$ for some $k \ge 1$.

These presentations are the fundamental groups of the closed orientable surface of genus $g$ and
the closed non-orientable surface of genus $k$; compact surfaces with boundary have free
fundamental groups.

Source: E.
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
