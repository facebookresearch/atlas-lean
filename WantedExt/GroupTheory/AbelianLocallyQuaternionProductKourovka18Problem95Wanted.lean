/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Products of abelian and locally quaternion groups (Kourovka Notebook Problem 18.95)

Kourovka Notebook, Archive of Solved Problems, Problem 18.95 (A. I. Sozutov): suppose that a group
`G = AB` is a product of an abelian subgroup `A` and a locally quaternion group `B` (that is, `B` is
a union of an increasing chain of finite generalized quaternion groups). Is `G` soluble?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.GroupTheory.AbelianLocallyQuaternionProductKourovka18Problem95Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.95 (A. I.
Sozutov). UnsolvedMath record UM-00701524 (`KOU-18.95`), dataset ulamai/UnsolvedMath v1.8.0.

Finite generalized quaternion groups are `QuaternionGroup (2 ^ k)` with `k ≥ 1`, of order `2^{k+2} ≥
8`; the chain is strictly increasing and `B` is its supremum, so `B` is infinite: the locally
quaternion group of Amberg-Sysak, which has a quasicyclic subgroup of index `2` (their Corollary 1.2
does not cover finite generalized quaternion `B`). `G = AB` means `AB = G` as sets.
-/

open scoped Pointwise

/-- `B` is locally quaternion: the union of a strictly increasing chain of finite generalized
quaternion groups `Q_{2^{k+2}}` (`QuaternionGroup (2 ^ k)`, `k ≥ 1`, of order `2^{k+2} ≥ 8`); in
particular `B` is infinite. -/
def IsLocallyQuaternion {G : Type} [Group G] (B : Subgroup G) : Prop :=
  ∃ Q : ℕ → Subgroup G, StrictMono Q ∧
    (∀ i, ∃ k : ℕ, 1 ≤ k ∧ Nonempty (Q i ≃* QuaternionGroup (2 ^ k))) ∧ B = ⨆ i, Q i

/-- Kourovka 18.95 (A. I. Sozutov): a group `G = AB` that is the product of an abelian subgroup `A`
and a locally quaternion subgroup `B` is soluble. -/
def abelianLocallyQuaternionProductSoluble : Prop :=
  ∀ (G : Type) [Group G] (A B : Subgroup G), (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
    IsLocallyQuaternion B → (A : Set G) * (B : Set G) = Set.univ → Group.IsSolvable G

/--
Resolved true: the Kourovka Archive answers 18.95 "Yes, it is" (B. Amberg and Ya. Sysak, 2017,
Corollary 1.2: a product of an abelian subgroup and a locally quaternion subgroup is soluble).
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.95 (A. I.
Sozutov); resolution: B. Amberg and Ya. Sysak, On products of groups with abelian subgroups of small
index, J. Group Theory 20 (2017), no. 6, 1061-1072, Kourovka Archive, Problem 18.95: Yes, it is;
Corollary 1.2 (arXiv:1611.10093): if a group G = AB is the product of an abelian subgroup A and a
locally quaternion subgroup B, then G is soluble (Theorem 1.1: derived length at most 3),
https://arxiv.org/abs/1611.10093.
-/
public theorem_wanted abelianLocallyQuaternionProductSoluble_holds :
    abelianLocallyQuaternionProductSoluble

end MathlibExt.GroupTheory.AbelianLocallyQuaternionProductKourovka18Problem95Wanted
