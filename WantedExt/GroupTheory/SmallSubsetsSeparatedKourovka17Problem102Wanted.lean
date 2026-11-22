/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Separation of small subsets of infinite groups (Kourovka Notebook Problem 17.102)

Kourovka Notebook, Problem 17.102 (I. V. Protasov): two subsets `A, B` of an infinite group `G` are
separated if there exists an infinite subset `X` of `G` such that `1 ∈ X`, `X = X⁻¹`, and `XAX ∩ B =
∅`. Is it true that any two disjoint subsets `A, B` of an infinite group `G` satisfying `|A| < |G|`,
`|B| < |G|` are separated?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

namespace MathlibExt.GroupTheory.SmallSubsetsSeparatedKourovka17Problem102Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 17.102 (I. V. Protasov). UnsolvedMath
record UM-00701404 (`KOU-17.102`), dataset ulamai/UnsolvedMath v1.8.0.

`XAX` is the pointwise product of sets and cardinalities are `Cardinal.mk`; groups are taken in
`Type`.
-/

open scoped Pointwise

/-- **Separated subsets of a group.** Two subsets $A$ and $B$ of a group $G$ are separated, in the
sense of I. V. Protasov, when there is an infinite subset $X \subseteq G$ with $1 \in X$,
$X^{-1} = X$ and $XAX \cap B = \emptyset$, where $XAX = \{x a y : x, y \in X,\ a \in A\}$. -/
def AreSeparated {G : Type*} [Group G] (A B : Set G) : Prop :=
  ∃ X : Set G, X.Infinite ∧ (1 : G) ∈ X ∧ X⁻¹ = X ∧ Disjoint (X * A * X) B

/-- **Separation of small disjoint subsets of infinite groups (Kourovka 17.102).** The statement,
posed by I. V. Protasov, that for every infinite group $G$ and all disjoint subsets
$A, B \subseteq G$ with $|A| < |G|$ and $|B| < |G|$, the sets $A$ and $B$ are separated. -/
def smallDisjointSubsetsSeparated : Prop :=
  ∀ (G : Type) [Group G] [Infinite G] (A B : Set G), Disjoint A B →
    Cardinal.mk A < Cardinal.mk G → Cardinal.mk B < Cardinal.mk G → AreSeparated A B

/--
**Small disjoint subsets of an infinite group need not be separated.** There exist an infinite
group $G$ and disjoint subsets $A, B \subseteq G$ with $|A| < |G|$ and $|B| < |G|$ such that $A$
and $B$ are not separated. That is, the statement of Kourovka Problem 17.102 is false.

Resolved false: Wan (Theorem 1.1) takes $G = \mathrm{Sym}(\mathbb{N})$ and splits the set of
transpositions into $A$ and $B$ using a graph on $\mathbb{N}$ with trivial automorphism group, so
that $|A| = |B| = \aleph_0 < 2^{\aleph_0}$. The Kourovka Notebook (21st issue) answers 17.102
"No, not always".

Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Problem 17.102 (I. V. Protasov); resolution: S. Wan, Counterexamples to Problem 17.102 of
The Kourovka Notebook, preprint, arXiv:2608.00504 (2026), Theorem 1.1 (an infinite group G with
disjoint A, B, |A|, |B| < |G|, not separated; in the proof G = Sym(N) and A, B split the
transpositions by a rigid graph on N); the Kourovka Notebook (21st issue) marks 17.102 solved (No,
not always), https://arxiv.org/abs/2608.00504.
-/
public theorem_wanted smallDisjointSubsetsSeparated_refuted : ¬ smallDisjointSubsetsSeparated

end MathlibExt.GroupTheory.SmallSubsetsSeparatedKourovka17Problem102Wanted
