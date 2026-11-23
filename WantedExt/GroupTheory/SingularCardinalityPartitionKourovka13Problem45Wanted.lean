/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Partitions of groups of singular cardinality (Kourovka Notebook Problem 13.45)

Kourovka Notebook, Archive of Solved Problems, Problem 13.45 (I. V. Protasov): every infinite group
`G` of regular cardinality `𝔪` can be partitioned as `G = A₁ ∪ A₂` so that `A₁ F ≠ G` and `A₂ F ≠ G`
for every `F ⊆ G` with `|F| < 𝔪`. Is this true for groups of singular cardinality?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

namespace MathlibExt.GroupTheory.SingularCardinalityPartitionKourovka13Problem45Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.45 (I. V.
Protasov). UnsolvedMath record UM-00700963 (`KOU-13.45`), dataset ulamai/UnsolvedMath v1.8.0.

The target is the statement for every infinite group of singular cardinality, with `A₁ F` the
pointwise product as in the problem. The resolving paper writes `F A₁`; its counterexamples are
abelian, where the two products agree. Singular means not regular (`Cardinal.IsRegular`) for the
infinite cardinal `#G`; groups are taken in `Type`.
-/

open Cardinal
open scoped Pointwise

/-- **Partitions of groups of singular cardinality (Kourovka 13.45).** The statement that every
infinite group $G$ whose cardinality $\mathfrak{m} = |G|$ is singular (not regular) can be split
into two disjoint sets $A_1$ and $A_2$ with $A_1 \cup A_2 = G$ such that $A_1 F \ne G$ and
$A_2 F \ne G$ for every subset $F \subseteq G$ with $|F| < \mathfrak{m}$, where
$A F = \{a f : a \in A, f \in F\}$. -/
def singularCardinalityPartition : Prop :=
  ∀ (G : Type) [Group G], Infinite G → ¬ (#G).IsRegular →
    ∃ A₁ A₂ : Set G, A₁ ∪ A₂ = Set.univ ∧ Disjoint A₁ A₂ ∧
      ∀ F : Set G, #F < #G → A₁ * F ≠ Set.univ ∧ A₂ * F ≠ Set.univ

/--
**Some group of singular cardinality has no such partition.** There is an infinite group $G$
whose cardinality $\mathfrak{m} = |G|$ is singular (not regular) such that for all disjoint sets
$A_1$ and $A_2$ with $A_1 \cup A_2 = G$ there is a subset $F \subseteq G$ with
$|F| < \mathfrak{m}$ and $A_1 F = G$ or $A_2 F = G$, where $A F = \{a f : a \in A, f \in F\}$.
That is, the statement of Kourovka Problem 13.45 fails.

Protasov and Slobodianiuk show that the answer depends on the algebraic structure of $G$: such a
partition exists for every free group, but not for abelian groups of singular cardinality. The
Kourovka Archive answers 13.45 "No, not always".

Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 13.45 (I. V. Protasov); resolution: I. Protasov and S.
Slobodianiuk, A note on partitions of groups, Quest. Answers Gen. Topology 33 (2015), no. 2, 61-70,
arXiv:1408.5607, abstract and Theorem 2(iii): the statement fails for abelian groups of singular
cardinality (it holds for free groups); Kourovka Archive, Problem 13.45,
https://arxiv.org/abs/1408.5607.
-/
public theorem_wanted singularCardinalityPartition_refuted : ¬ singularCardinalityPartition

end MathlibExt.GroupTheory.SingularCardinalityPartitionKourovka13Problem45Wanted
