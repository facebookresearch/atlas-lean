/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Free products of elementarily equivalent groups (Kourovka Notebook Problem 9.66)

Kourovka Notebook, Problem 9.66 (A. D. Taimanov), marked solved in the 21st issue: a) B. Jónsson's
conjecture: elementary equivalence is preserved under taking free products in the class of all
groups, that is, if `Th(G₁) = Th(G₂)` and `Th(H₁) = Th(H₂)`, then `Th(G₁ ∗ H₁) = Th(G₂ ∗ H₂)`. b) A
weakened conjecture for countable groups about the `m`- and Turing degrees of the sets of numbers of
theorems of `Th(Gᵢ ∗ Hᵢ)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Coprod.Basic
public import MathlibExt.ModelTheory.GroupLanguage

@[expose] public section

namespace MathlibExt.ModelTheory.FreeProductElementaryEquivalenceKourovka9Problem66Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 9.66 (A. D. Taimanov). UnsolvedMath record
UM-00700599 (`KOU-9.66`), dataset ulamai/UnsolvedMath v1.8.0.

Only part (a) is formalized; part (b) is a weakening of (a) about degrees of unsolvability.
Elementary equivalence is Mathlib's `ElementarilyEquivalent` for the first-order language of groups
`groupLanguage` (MathlibExt) with the canonical structures; the free product is `Monoid.Coprod`.
-/

open FirstOrder Language

/-- Kourovka 9.66(a) (A. D. Taimanov; B. Jónsson's conjecture): elementary equivalence of groups is
preserved by free products: if `G₁ ≡ G₂` and `H₁ ≡ H₂`, then `G₁ ∗ H₁ ≡ G₂ ∗ H₂`. -/
def freeProductPreservesElementaryEquivalence : Prop :=
  ∀ (G₁ G₂ H₁ H₂ : Type) [Group G₁] [Group G₂] [Group H₁] [Group H₂],
    (letI := groupLanguageStructure G₁; letI := groupLanguageStructure G₂;
      groupLanguage.ElementarilyEquivalent G₁ G₂) →
    (letI := groupLanguageStructure H₁; letI := groupLanguageStructure H₂;
      groupLanguage.ElementarilyEquivalent H₁ H₂) →
    (letI := groupLanguageStructure (Monoid.Coprod G₁ H₁);
      letI := groupLanguageStructure (Monoid.Coprod G₂ H₂);
      groupLanguage.ElementarilyEquivalent (Monoid.Coprod G₁ H₁) (Monoid.Coprod G₂ H₂))

/--
Resolved true: Sela answers affirmatively Vaught's question on the elementary equivalence of free
products of pairs of elementarily equivalent groups; the Kourovka Notebook (21st issue) marks 9.66
solved: the conjecture (Jónsson's, also known as Vaught's) is proved. Source: E. I. Khukhro and V.
D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Problem 9.66 (A. D. Taimanov); resolution: Z. Sela, Diophantine geometry
over groups X: The elementary theory of free products of groups, arXiv:1012.0044 (2010), abstract:
an affirmative answer to R. L. Vaught's question on the elementary equivalence of free products of
pairs of elementarily equivalent groups; the Kourovka Notebook (21st issue) marks 9.66 solved: "The
conjecture (also known as R. L. Vaught's conjecture) is proved", https://arxiv.org/abs/1012.0044.
-/
public theorem_wanted freeProductPreservesElementaryEquivalence_holds :
    freeProductPreservesElementaryEquivalence

end MathlibExt.ModelTheory.FreeProductElementaryEquivalenceKourovka9Problem66Wanted
