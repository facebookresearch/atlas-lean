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

/-- **Locally quaternion subgroup.** A subgroup $B$ of a group $G$ is locally quaternion if there
is a strictly increasing sequence $C_0 < C_1 < C_2 < \cdots$ of subgroups of $G$, each isomorphic
to a generalized quaternion group $Q_{2^{k+2}}$ of order $2^{k+2}$ for some $k \ge 1$, whose
supremum (for a chain, the union) is $B$. In particular $B$ is infinite. -/
def IsLocallyQuaternion {G : Type} [Group G] (B : Subgroup G) : Prop :=
  ∃ Q : ℕ → Subgroup G, StrictMono Q ∧
    (∀ i, ∃ k : ℕ, 1 ≤ k ∧ Nonempty (Q i ≃* QuaternionGroup (2 ^ k))) ∧ B = ⨆ i, Q i

/-- **Kourovka Problem 18.95 (Sozutov).** The proposition that every group $G$ with subgroups $A$
and $B$ such that $A$ is abelian, $B$ is locally quaternion, and $G = AB$ (every element of $G$ is a
product $ab$ with $a \in A$ and $b \in B$) is soluble. -/
def abelianLocallyQuaternionProductSoluble : Prop :=
  ∀ (G : Type) [Group G] (A B : Subgroup G), (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
    IsLocallyQuaternion B → (A : Set G) * (B : Set G) = Set.univ → Group.IsSolvable G

/--
**Products of abelian and locally quaternion groups are soluble.** Let $G$ be a group with
subgroups $A$ and $B$ such that $A$ is abelian, $B$ is locally quaternion, and $G = AB$, that is,
every element of $G$ is a product $ab$ with $a \in A$ and $b \in B$. Then $G$ is soluble.

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
