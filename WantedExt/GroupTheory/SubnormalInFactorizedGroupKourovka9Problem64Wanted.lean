/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Subnormal subgroups of both factors of a product (Kourovka Notebook Problem 9.64)

Kourovka Notebook, Archive of Solved Problems, Problem 9.64 (Ya. P. Sysak): is it true that, in a
group of the form `G = AB`, every subgroup `N` of `A ∩ B` which is subnormal both in `A` and in `B`
is subnormal in `G`? The answer is affirmative for finite groups (H. Wielandt).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.IsSubnormal

@[expose] public section

namespace MathlibExt.GroupTheory.SubnormalInFactorizedGroupKourovka9Problem64Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.64 (Ya. P.
Sysak). UnsolvedMath record UM-00700597 (`KOU-9.64`), dataset ulamai/UnsolvedMath v1.8.0.

`G = AB` means `(A : Set G) * B = univ`; subnormality is Mathlib's `Subgroup.IsSubnormal`, inside
`A` and `B` via `subgroupOf`. Groups are arbitrary groups in `Type`.
-/

open scoped Pointwise

/-- Kourovka 9.64 (Ya. P. Sysak): in a group `G = AB`, every subgroup `N ≤ A ∩ B` that is subnormal
in `A` and in `B` is subnormal in `G`. -/
def subnormalInBothFactorsSubnormal : Prop :=
  ∀ (G : Type) [Group G] (A B N : Subgroup G), (A : Set G) * (B : Set G) = Set.univ → N ≤ A ⊓ B →
    (N.subgroupOf A).IsSubnormal → (N.subgroupOf B).IsSubnormal → N.IsSubnormal

/--
Resolved false: Casolo and Dardano give a group `G = UV` with a cyclic subgroup `H` of `U ∩ V` that
is subnormal of defect `2` in `U` and in `V` but not even serial, hence not subnormal, in `G`
(zbMATH review Zbl 1074.20018); the Kourovka Archive answers 9.64 "No, not always" (for finite
groups the answer is yes, by Wielandt). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 9.64 (Ya. P. Sysak); resolution: C. Casolo and U. Dardano, Subnormality in
the join of two subgroups, J. Group Theory 7 (2004), 507-520, zbMATH review Zbl 1074.20018: an
example of a factorized group G = UV with a cyclic subgroup H of U ∩ V that is subnormal of defect 2
in U and in V but not even serial in G; Kourovka Archive of Solved Problems, Problem 9.64: No, not
always, https://doi.org/10.1515/jgth.2004.7.4.507.
-/
public theorem_wanted subnormalInBothFactorsSubnormal_refuted : ¬ subnormalInBothFactorsSubnormal

end MathlibExt.GroupTheory.SubnormalInFactorizedGroupKourovka9Problem64Wanted
