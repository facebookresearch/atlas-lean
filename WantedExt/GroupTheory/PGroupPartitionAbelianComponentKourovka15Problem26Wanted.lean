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

/-- `C` is a partition of `G`: a family of proper subgroups (components) whose union is `G` and
which intersect pairwise trivially. -/
def IsGroupPartition {G : Type*} [Group G] (C : Set (Subgroup G)) : Prop :=
  (∀ H ∈ C, H ≠ ⊤) ∧ (∀ g : G, ∃ H ∈ C, g ∈ H) ∧ ∀ H ∈ C, ∀ K ∈ C, H ≠ K → H ⊓ K = ⊥

/-- Kourovka 15.26 (Ya. G. Berkovich): every partition of a finite `p`-group has an abelian
component. -/
def pGroupPartitionHasAbelianComponent : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G], IsPGroup p G →
    ∀ C : Set (Subgroup G), IsGroupPartition C → ∃ H ∈ C, ∀ x ∈ H, ∀ y ∈ H, x * y = y * x

/--
Resolved true: by Theorem B of Cat's preprint, every partition of a finite `p`-group into nontrivial
components has an abelian component (for non-abelian `G` an elementary abelian one meeting `Φ(G)`
trivially); the Kourovka Notebook (21st issue) marks 15.26 solved, "Yes, it is true" (AI solution
confirmed by E. I. Khukhro). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.26 (Ya. G.
Berkovich); resolution: G. Cat, A Frattini-free component in every partition, and Kourovka 15.26,
preprint (2026), AI-generated solution confirmed by E. I. Khukhro, Theorem B (a partition of a
finite p-group into nontrivial components has an abelian component), derived from Theorem A; the
Kourovka Notebook (21st issue) marks 15.26 solved,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/08/kourovka_15-26-ai.pdf.
-/
public theorem_wanted pGroupPartitionHasAbelianComponent_holds : pGroupPartitionHasAbelianComponent

end MathlibExt.GroupTheory.PGroupPartitionAbelianComponentKourovka15Problem26Wanted
