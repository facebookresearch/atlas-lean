/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Squarelike and discriminating groups (Kourovka Notebook Problem 15.86)

Kourovka Notebook, Archive of Solved Problems, Problem 15.86 (D. Spellman): a group `G` is
discriminating if for any finite set of nontrivial elements of `G × G` there is a homomorphism `G ×
G → G` which annihilates none of them, and squarelike if it is universally equivalent to a
discriminating group. Must every squarelike group be elementarily equivalent to a discriminating
group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.ModelTheory.Complexity
public import MathlibExt.ModelTheory.GroupLanguage

@[expose] public section

namespace MathlibExt.ModelTheory.SquarelikeDiscriminatingGroupKourovka15Problem86Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.86 (D.
Spellman). UnsolvedMath record UM-00701174 (`KOU-15.86`), dataset ulamai/UnsolvedMath v1.8.0.

First-order logic uses MathlibExt's `groupLanguage` (multiplication, inverse, identity) with the
canonical structure on a group. Universal equivalence compares the universal sentences
(`BoundedFormula.IsUniversal`: universal quantifiers in front of a quantifier-free formula), and
elementary equivalence is Mathlib's `ElementarilyEquivalent` (the same complete theory) for these
structures. Groups are taken in `Type`.
-/

open FirstOrder FirstOrder.Language

/-- `G` is discriminating: for every finite set of nontrivial elements of `G × G` some
homomorphism `G × G → G` maps none of them to `1`. -/
def IsDiscriminating (G : Type*) [Group G] : Prop :=
  ∀ S : Finset (G × G), (∀ x ∈ S, x ≠ 1) → ∃ f : G × G →* G, ∀ x ∈ S, f x ≠ 1

/-- `G` satisfies the first-order sentence `φ` of the language of groups. -/
def SatisfiesSentence (G : Type) [Group G] (φ : groupLanguage.Sentence) : Prop :=
  @Sentence.Realize groupLanguage G (groupLanguageStructure G) φ

/-- `G` and `H` satisfy the same universal sentences of the language of groups. -/
def UniversallyEquivalent (G H : Type) [Group G] [Group H] : Prop :=
  ∀ φ : groupLanguage.Sentence, BoundedFormula.IsUniversal φ →
    (SatisfiesSentence G φ ↔ SatisfiesSentence H φ)

/-- Kourovka 15.86 (D. Spellman): every squarelike group (one universally equivalent to a
discriminating group) is elementarily equivalent to a discriminating group. -/
def squarelikeElementarilyEquivalentToDiscriminating : Prop :=
  ∀ (G : Type) [Group G],
    (∃ (D : Type) (_ : Group D), IsDiscriminating D ∧ UniversallyEquivalent G D) →
      ∃ (D : Type) (_ : Group D), IsDiscriminating D ∧
        (letI := groupLanguageStructure G; letI := groupLanguageStructure D;
          groupLanguage.ElementarilyEquivalent G D)

/--
Resolved true: Belegradek proved that every square-like group is elementarily equivalent to a
countable discriminating group (see also Fine, Gaglione and Spellman); the Kourovka Archive answers
15.86 "Yes, it must". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 15.86 (D. Spellman); resolution: O. Belegradek, Discriminating and square-like groups, J.
Group Theory 7 (2004), no. 4, 521-532; B. Fine, A. M. Gaglione and D. Spellman, Arch. Math. 83
(2004), no. 2, 106-112, Belegradek, abstract (any square-like group is elementarily equivalent to a
countable discriminating group); Kourovka Archive, Problem 15.86 (answer: Yes, it must).
-/
public theorem_wanted squarelikeElementarilyEquivalentToDiscriminating_holds :
    squarelikeElementarilyEquivalentToDiscriminating

end MathlibExt.ModelTheory.SquarelikeDiscriminatingGroupKourovka15Problem86Wanted
