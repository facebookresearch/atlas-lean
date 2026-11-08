/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Countable dense partitions without expansive sequences (Kourovka Notebook Problem 15.80)

Kourovka Notebook, Problem 15.80 (I. V. Protasov): a sequence `{Fₙ}` of pairwise disjoint finite
subsets of a topological group is expansive if for every open subset `U` there is `m` such that `Fₙ
∩ U ≠ ∅` for all `n > m`. Suppose that a group `G` can be partitioned into countably many dense
subsets. Is it true that `G` has an expansive sequence?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.Group.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.DensePartitionExpansiveSequenceKourovka15Problem80Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.80 (I. V. Protasov). UnsolvedMath record
UM-00701168 (`KOU-15.80`), dataset ulamai/UnsolvedMath v1.8.0.

`G` is a topological group (`IsTopologicalGroup`, not necessarily Hausdorff). "Every open subset"
means every nonempty open subset, since the empty set meets nothing. "Countably many" is read as a
partition indexed by `ℕ` into pairwise disjoint dense sets, the most restrictive reading of the
hypothesis, so the refutation is the strongest one; such a partition has infinitely many nonempty
cells.
-/

/-- A sequence of pairwise disjoint finite sets `F n` is expansive if every nonempty open set meets
`F n` for all large `n`. -/
def IsExpansiveSequence {G : Type*} [TopologicalSpace G] (F : ℕ → Finset G) : Prop :=
  Pairwise (fun i j => Disjoint (F i) (F j)) ∧
    ∀ U : Set G, IsOpen U → U.Nonempty → ∃ m : ℕ, ∀ n, m < n → ∃ x ∈ F n, x ∈ U

/-- Kourovka 15.80 (I. V. Protasov): every topological group that can be partitioned into countably
many dense subsets has an expansive sequence. -/
def countableDensePartitionHasExpansiveSequence : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    (∃ P : ℕ → Set G, Pairwise (fun i j => Disjoint (P i) (P j)) ∧ (⋃ i, P i) = Set.univ ∧
      ∀ i, Dense (P i)) → ∃ F : ℕ → Finset G, IsExpansiveSequence F

/--
Resolved false: the Kourovka Notebook (21st issue) answers 15.80 "Not necessarily" (S. Corson): `∏_ℕ
ℝ` with the box topology has no countable dense subset, hence no expansive sequence (the union of
one is countable and dense), but its base of `2^ℵ₀` open sets of size `2^ℵ₀` lets a transfinite
induction partition it into countably many dense subsets. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Problem 15.80 (I. V. Protasov); resolution: S. Corson, letter of 19 May 2025, as recorded in
the Kourovka Notebook (21st issue), Problem 15.80, G = ∏_ℕ ℝ with the box topology: not separable,
hence without expansive sequences, but partitionable into countably many dense subsets by
transfinite induction; the Kourovka Notebook (21st issue) marks 15.80 solved (answer: Not
necessarily), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted countableDensePartitionHasExpansiveSequence_refuted :
    ¬ countableDensePartitionHasExpansiveSequence

end MathlibExt.GroupTheory.DensePartitionExpansiveSequenceKourovka15Problem80Wanted
