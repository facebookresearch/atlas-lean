/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Embedding ordered groups into ordered groups with three classes (Kourovka Notebook Problem 11.68)

Kourovka Notebook, Archive of Solved Problems, Problem 11.68 (B. Neumann): can every fully ordered
group be embedded in a fully ordered group (continuing the given order) with only 3 classes of
conjugate elements?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Conj
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.OrderedGroupThreeClassesEmbeddingKourovka11Problem68Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.68 (B.
Neumann). UnsolvedMath record UM-00700760 (`KOU-11.68`), dataset ulamai/UnsolvedMath v1.8.0.

A fully ordered group is a group with a two-sided invariant linear order: Mathlib's `MulLeftMono`
and `MulRightMono` (`a ≤ b` implies `c * a ≤ c * b` and `a * c ≤ b * c`). "Continuing the given
order" is an order-preserving (strictly monotone, hence injective) homomorphism. "Only 3 classes" is
exactly 3: a nontrivial ordered group has at least the three classes `{1}`, the positive class and
the negative class.
-/

/-- Kourovka 11.68 (B. Neumann): every fully ordered group embeds, by an order-preserving
homomorphism, into a fully ordered group with exactly three conjugacy classes. -/
def orderedEmbedsInThreeClasses : Prop :=
  ∀ (G : Type) [Group G] [LinearOrder G] [MulLeftMono G] [MulRightMono G],
    ∃ (H : Type) (_ : Group H) (_ : LinearOrder H), MulLeftMono H ∧ MulRightMono H ∧
      Nat.card (ConjClasses H) = 3 ∧ ∃ f : G →* H, StrictMono f

/--
Resolved false: the Kourovka Archive answers 11.68 "No, not every" (Bludov): some fully ordered
group admits no order-preserving embedding into a fully ordered group with exactly three conjugacy
classes. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.68
(B. Neumann); resolution: V. V. Bludov, Algebra and Logic 44, no. 6 (2005), 370-380, Kourovka
Archive, Problem 11.68: "No, not every", https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted orderedEmbedsInThreeClasses_refuted : ¬ orderedEmbedsInThreeClasses

end MathlibExt.GroupTheory.OrderedGroupThreeClassesEmbeddingKourovka11Problem68Wanted
