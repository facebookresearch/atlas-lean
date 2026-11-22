/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Products of two divisible abelian `p`-groups of finite rank (Kourovka Notebook Problem 1.78)

Kourovka Notebook, Archive of Solved Problems, Problem 1.78 (N. F. Sesekin): let a group `G` be the
product of two divisible abelian `p`-groups of finite rank. Is `G` itself a divisible abelian
`p`-group of finite rank?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.ProductDivisibleAbelianPGroupsKourovka1Problem78Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.78 (N. F.
Sesekin). UnsolvedMath record UM-00700068 (`KOU-1.78`), dataset ulamai/UnsolvedMath v1.8.0.

The two factors are subgroups `A` and `B` with `G = AB` (every element is a product `ab`). Divisible
means that every element has an `n`-th root for every `n ≥ 1`. The rank of an abelian `p`-group is
the dimension over `𝔽_p` of its socle `{x | x ^ p = 1}`, so finite rank means that this socle is
finite.
-/

/-- `G` is a divisible abelian `p`-group of finite rank: all elements commute, every element has
`p`-power order, every element has an `n`-th root for every `n ≥ 1`, and only finitely many
elements satisfy `x ^ p = 1` (the rank of an abelian `p`-group is the dimension of this socle). -/
def IsDivisibleAbelianPGroupFiniteRank (p : ℕ) (G : Type*) [Group G] : Prop :=
  (∀ x y : G, x * y = y * x) ∧ IsPGroup p G ∧ (∀ (x : G) (n : ℕ), 0 < n → ∃ y : G, y ^ n = x) ∧
    {x : G | x ^ p = 1}.Finite

/-- Kourovka 1.78 (N. F. Sesekin): if a group `G` is the product `G = AB` of two subgroups `A` and
`B` that are divisible abelian `p`-groups of finite rank, then `G` is itself a divisible abelian
`p`-group of finite rank. -/
def productOfDivisibleAbelianPGroups : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] (A B : Subgroup G),
    IsDivisibleAbelianPGroupFiniteRank p A → IsDivisibleAbelianPGroupFiniteRank p B →
    (∀ g : G, ∃ a ∈ A, ∃ b ∈ B, g = a * b) → IsDivisibleAbelianPGroupFiniteRank p G

/--
Resolved true: the Kourovka Archive answers 1.78 Yes (printed "Yet, it is"), citing Sesekin (1968):
a group that is the product of two divisible abelian `p`-groups of finite rank is itself a divisible
abelian `p`-group of finite rank. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems
in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 1.78 (N. F. Sesekin); resolution: N. F. Sesekin, Siberian Math. J. 9 (1968),
1070-1072, Kourovka Archive, Problem 1.78 (answer printed "Yet, it is", i.e. Yes).
-/
public theorem_wanted productOfDivisibleAbelianPGroups_holds : productOfDivisibleAbelianPGroups

end MathlibExt.GroupTheory.ProductDivisibleAbelianPGroupsKourovka1Problem78Wanted
