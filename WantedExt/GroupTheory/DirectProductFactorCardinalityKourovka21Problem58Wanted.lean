/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cardinalities of maximal direct factors in infinite groups (Kourovka Notebook Problem 21.58)

Kourovka Notebook, Problem 21.58 (M. H. Hooshmand), marked solved in the 21st issue: we say that a
product `XY = {xy | x ∈ X, y ∈ Y}` of two subsets `X, Y` of a group `G` is direct if for every `z ∈
XY` there are unique `x ∈ X`, `y ∈ Y` such that `z = xy`. Is there an infinite group `G` such that
every subset `A ⊆ G` satisfies the following property: all the maximal subsets `B` for which the
product `AB` is direct have the same cardinality?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.SetTheory.Cardinal.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.DirectProductFactorCardinalityKourovka21Problem58Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 21.58 (M. H. Hooshmand). UnsolvedMath
record UM-00002567 (`KOU-21.58`), dataset ulamai/UnsolvedMath v1.8.0.

Maximal is Mathlib's `Maximal` for inclusion of subsets; cardinalities are `Cardinal.mk`. Groups are
taken in `Type`.
-/

/-- The product `A B` of subsets of `G` is direct: each element of `A B` is `a b` for unique
`a ∈ A` and `b ∈ B`. -/
def IsDirectProduct {G : Type} [Group G] (A B : Set G) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ B, ∀ b₂ ∈ B, a₁ * b₁ = a₂ * b₂ → a₁ = a₂ ∧ b₁ = b₂

/-- Kourovka 21.58 (M. H. Hooshmand): there is an infinite group `G` such that, for every subset
`A ⊆ G`, all maximal subsets `B` for which the product `A B` is direct have the same
cardinality. -/
def existsInfiniteGroupStableFactors : Prop :=
  ∃ (G : Type) (_ : Group G), Infinite G ∧ ∀ A B₁ B₂ : Set G,
    Maximal (IsDirectProduct A) B₁ → Maximal (IsDirectProduct A) B₂ →
      Cardinal.mk B₁ = Cardinal.mk B₂

/--
Resolved false: Kabenyuk (Section 6) proves that every infinite group has a subset `A` for which the
maximal subsets `B` with `AB` direct do not all have the same cardinality; the 21st issue of the
Kourovka Notebook marks 21.58 solved ("No, there are no such groups"), citing also Hooshmand,
arXiv:2604.08724, Remark 1.16. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 21.58 (M. H.
Hooshmand); resolution: M. I. Kabenyuk, Factors in infinite groups, preprint, arXiv:2602.22876
(2026); M. H. Hooshmand, preprint, arXiv:2604.08724 (2026), Remark 1.16, Kabenyuk, Section 6,
Theorem: every infinite group is unstable, i.e. has a subset A whose maximal subsets U with AU
direct do not all have the same cardinality; Kourovka Notebook (21st issue), Problem 21.58: No,
there are no such groups, https://arxiv.org/abs/2602.22876.
-/
public theorem_wanted existsInfiniteGroupStableFactors_refuted : ¬ existsInfiniteGroupStableFactors

end MathlibExt.GroupTheory.DirectProductFactorCardinalityKourovka21Problem58Wanted
