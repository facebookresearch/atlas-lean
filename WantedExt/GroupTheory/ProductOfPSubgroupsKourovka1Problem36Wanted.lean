/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Groups factorized by two `p`-subgroups (Kourovka Notebook Problem 1.36)

Kourovka Notebook, Archive of Solved Problems, Problem 1.36 (Sh. S. Kemkhadze): if a group `G` is
factorizable by `p`-subgroups, that is, `G = AB` where `A` and `B` are `p`-subgroups, does it follow
that `G` is itself a `p`-group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.ProductOfPSubgroupsKourovka1Problem36Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.36 (Sh. S.
Kemkhadze). UnsolvedMath record UM-00700031 (`KOU-1.36`), dataset ulamai/UnsolvedMath v1.8.0.

A `p`-group is one in which every element has `p`-power order (`IsPGroup`), for a prime `p`; `G =
AB` means every element is a product `ab` with `a ∈ A`, `b ∈ B`. The target is stated for every
prime `p`, so its refutation gives a counterexample for some prime. For finite `G` the answer is
yes, so the counterexample is infinite.
-/

/-- Kourovka 1.36 (Sh. S. Kemkhadze): if a group `G` is the product `G = AB` of two `p`-subgroups
`A` and `B` (every element of `p`-power order), then `G` is a `p`-group. -/
def productOfPSubgroupsIsPGroup : Prop :=
  ∀ (p : ℕ) (G : Type) [Group G] (A B : Subgroup G), p.Prime → IsPGroup p A → IsPGroup p B →
    (∀ g : G, ∃ a ∈ A, ∃ b ∈ B, g = a * b) → IsPGroup p G

/--
Resolved false: the Kourovka Archive answers 1.36 "Not always", citing Sysak's construction of a
group `G = AB` with `p`-subgroups `A`, `B` that is not a `p`-group. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 1.36 (Sh. S. Kemkhadze); resolution:
Ya. P. Sysak, Products of infinite groups, Math. Inst. Akad. Nauk Ukrain. SSR, Kiev, 1982 (Russian),
Kourovka Archive, Problem 1.36 (Not always).
-/
public theorem_wanted productOfPSubgroupsIsPGroup_refuted : ¬ productOfPSubgroupsIsPGroup

end MathlibExt.GroupTheory.ProductOfPSubgroupsKourovka1Problem36Wanted
