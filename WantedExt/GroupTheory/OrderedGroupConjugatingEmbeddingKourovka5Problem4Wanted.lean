/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Conjugating positive elements in extensions of ordered groups (Kourovka Notebook Problem 5.4)

Kourovka Notebook, Archive of Solved Problems, Problem 5.4 (V. V. Bludov): let g and h be positive
elements of a linearly ordered group G; can one always embed G in a linearly ordered group in such a
way that g and h are conjugate?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.OrderedGroupConjugatingEmbeddingKourovka5Problem4Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.4 (V. V.
Bludov). UnsolvedMath record UM-00700288 (`KOU-5.4`), dataset ulamai/UnsolvedMath v1.8.0.

A linearly ordered group is a group with a total order invariant under left and right multiplication
(`LinearOrder`, `MulLeftMono`, `MulRightMono`); an embedding is an injective homomorphism preserving
the order, here a strictly monotone homomorphism.
-/

/-- Kourovka 5.4 (V. V. Bludov): for positive elements `g`, `h` of a linearly ordered group `G`
(a group with a total order invariant under left and right multiplication), `G` embeds in a
linearly ordered group in which the images of `g` and `h` are conjugate (an injective, strictly
monotone homomorphism). -/
def positiveElementsConjugateInExtension : Prop :=
  ∀ (G : Type) [Group G] [LinearOrder G] [MulLeftMono G] [MulRightMono G] (g h : G),
    1 < g → 1 < h → ∃ (H : Type) (_ : Group H) (_ : LinearOrder H) (_ : MulLeftMono H)
      (_ : MulRightMono H) (f : G →* H), StrictMono f ∧ IsConj (f g) (f h)

/--
Resolved false: the Kourovka Archive answers 5.4 "No, not always", citing Bludov, Completion of
linearly ordered groups (Algebra and Logic 44 (2005), 370-380): some linearly ordered group has
positive elements `g`, `h` that are conjugate in no linearly ordered group containing it. Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.4 (V. V. Bludov);
resolution: V. V. Bludov, Completion of linearly ordered groups, Algebra and Logic 44 (2005),
370-380, Kourovka Archive, Problem 5.4: No, not always (Bludov),
https://doi.org/10.1007/s10469-005-0036-6.
-/
public theorem_wanted positiveElementsConjugateInExtension_refuted :
    ¬ positiveElementsConjugateInExtension

end MathlibExt.GroupTheory.OrderedGroupConjugatingEmbeddingKourovka5Problem4Wanted
