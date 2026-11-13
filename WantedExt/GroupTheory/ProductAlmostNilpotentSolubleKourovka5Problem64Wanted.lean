/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Products of two almost nilpotent groups (Kourovka Notebook Problem 5.64)

Kourovka Notebook, Archive of Solved Problems, Problem 5.64 (L. A. Shemetkov): suppose that a finite
group G is the product of two subgroups A₁ and A₂. Prove that if Aᵢ contains a nilpotent subgroup of
index ≤ 2 for i = 1, 2, then G is soluble.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.ProductAlmostNilpotentSolubleKourovka5Problem64Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.64 (L. A.
Shemetkov). UnsolvedMath record UM-00700343 (`KOU-5.64`), dataset ulamai/UnsolvedMath v1.8.0.

`G = A₁ A₂` is the set product `(A₁ : Set G) * A₂ = Set.univ`; a nilpotent subgroup of index at most
`2` in `Aᵢ` is `N ≤ Aᵢ` with `Group.IsNilpotent N` and `N.relIndex Aᵢ ≤ 2` (the index is finite as
`G` is finite).
-/

open scoped Pointwise

/-- Kourovka 5.64 (L. A. Shemetkov): if a finite group `G = A₁ A₂` is the product of two subgroups
each containing a nilpotent subgroup of index at most `2`, then `G` is soluble. -/
def productAlmostNilpotentSoluble : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A B : Subgroup G), (A : Set G) * (B : Set G) = Set.univ →
    (∃ N : Subgroup G, N ≤ A ∧ Group.IsNilpotent N ∧ N.relIndex A ≤ 2) →
    (∃ N : Subgroup G, N ≤ B ∧ Group.IsNilpotent N ∧ N.relIndex B ≤ 2) →
    Group.IsSolvable G

/--
Resolved true: Kazarin (1981) proves that a finite group `G = A₁ A₂` whose factors each contain a
nilpotent subgroup of index at most `2` is soluble, and the Kourovka Archive records 5.64 as proved
by Kazarin. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.64
(L. A. Shemetkov); resolution: L. S. Kazarin, On the product of two groups that are close to being
nilpotent, Math. USSR-Sb. 38 (1981), 47-59, Theorem (abstract): a finite group representable as the
product of two subgroups, each of which has a nilpotent subgroup of index at most 2, is solvable;
Kourovka Archive, Problem 5.64: This has been proved (Kazarin),
https://doi.org/10.1070/SM1981v038n01ABEH001216.
-/
public theorem_wanted productAlmostNilpotentSoluble_holds : productAlmostNilpotentSoluble

end MathlibExt.GroupTheory.ProductAlmostNilpotentSolubleKourovka5Problem64Wanted
