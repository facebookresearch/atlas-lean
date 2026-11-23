/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Abelian components of partitions of finite `p`-groups (Kourovka Notebook Problem 15.26)

Kourovka Notebook, Problem 15.26 (Ya. G. Berkovich): a partition of a group is a representation of
it as a set-theoretic union of some of its proper subgroups (components) that intersect pairwise
trivially. Is it true that every nontrivial partition of a finite `p`-group has an abelian
component?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.PGroupPartitionAbelianComponentKourovka15Problem26Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.26 (Ya. G. Berkovich). UnsolvedMath
record UM-00701114 (`KOU-15.26`), dataset ulamai/UnsolvedMath v1.8.0.

Components are proper subgroups that cover `G` and meet pairwise in `1`. They are not required to be
nontrivial, as in Theorem A of the resolving preprint: a trivial component is abelian, and removing
it leaves a partition. A partition always has at least two components, so "nontrivial" adds no
condition.
-/

/-- **Partition of a group.** Let $G$ be a group. A set $C$ of subgroups of $G$ is a partition of
$G$ when every member of $C$ is a proper subgroup of $G$, every element of $G$ lies in some member
of $C$, and any two distinct members of $C$ intersect in the trivial subgroup. The members of $C$
are called its components. -/
def IsGroupPartition {G : Type*} [Group G] (C : Set (Subgroup G)) : Prop :=
  (∀ H ∈ C, H ≠ ⊤) ∧ (∀ g : G, ∃ H ∈ C, g ∈ H) ∧ ∀ H ∈ C, ∀ K ∈ C, H ≠ K → H ⊓ K = ⊥

/-- **Berkovich's question on abelian components of partitions.** The statement that for every prime
$p$, every finite $p$-group $G$ and every partition $C$ of $G$ (a set of proper subgroups of $G$
whose union is $G$ and any two distinct members of which intersect in the trivial subgroup), some
member $H$ of $C$ is abelian, that is, $xy = yx$ for all $x, y \in H$.

This is Kourovka Notebook Problem 15.26 (Ya. G. Berkovich). -/
def pGroupPartitionHasAbelianComponent : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G], IsPGroup p G →
    ∀ C : Set (Subgroup G), IsGroupPartition C → ∃ H ∈ C, ∀ x ∈ H, ∀ y ∈ H, x * y = y * x

/--
**Every partition of a finite $p$-group has an abelian component.** For every prime $p$, every
finite $p$-group $G$ and every partition $C$ of $G$ (a set of proper subgroups of $G$ whose union is
$G$ and any two distinct members of which intersect in the trivial subgroup), some member $H$ of $C$
is abelian, that is, $xy = yx$ for all $x, y \in H$.

Resolved true: by Theorem B of Cat's preprint, every partition of a finite $p$-group into nontrivial
components has an abelian component (for non-abelian $G$ an elementary abelian one meeting the
Frattini subgroup $\Phi(G)$ of $G$ trivially); the Kourovka Notebook (21st issue) marks 15.26
solved, "Yes, it is true" (AI solution confirmed by E. I. Khukhro). Components are not required to
be nontrivial here: a trivial component is abelian, and removing it leaves a partition.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.26 (Ya. G. Berkovich); resolution: G.
Cat, A Frattini-free component in every partition, and Kourovka 15.26, preprint (2026), AI-generated
solution confirmed by E. I. Khukhro, Theorem B (a partition of a finite p-group into nontrivial
components has an abelian component), derived from Theorem A; the Kourovka Notebook (21st issue)
marks 15.26 solved,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/08/kourovka_15-26-ai.pdf.
-/
public theorem_wanted pGroupPartitionHasAbelianComponent_holds : pGroupPartitionHasAbelianComponent

end MathlibExt.GroupTheory.PGroupPartitionAbelianComponentKourovka15Problem26Wanted
