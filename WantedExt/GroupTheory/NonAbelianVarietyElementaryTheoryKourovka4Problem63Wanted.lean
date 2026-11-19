/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Non-abelian varieties with decidable elementary theory (Kourovka Notebook Problem 4.63)

Kourovka Notebook, Archive of Solved Problems, Problem 4.63 (A. Tarski): does there exist a
non-abelian variety of groups (in particular, one that contains the variety of all abelian groups)
whose elementary theory is decidable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE
public import WantedExt.GroupTheory.FormationVarietyPGroupsKourovka11Problem21Wanted
public import WantedExt.GroupTheory.PrenexSentenceShared

@[expose] public section

namespace MathlibExt.GroupTheory.NonAbelianVarietyElementaryTheoryKourovka4Problem63Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.63 (A.
Tarski). UnsolvedMath record UM-00700270 (`KOU-4.63`), dataset ulamai/UnsolvedMath v1.8.0.

Laws and varieties are `SatisfiesLaws` of the Kourovka 11.21 entry, reused here: a law is a word of
`FreeGroup ℕ`, the variety defined by a set `W` of laws consists of the groups in which every law of
`W` holds, and every variety arises this way. The elementary theory of a variety is the set of
first-order sentences of the language of groups true in all of its groups. Sentences are the codes
`PrenexSentence` of `PrenexSentenceShared` (shared with the Kourovka 1.29 and 16.71 entries): a
quantifier prefix binding `x₀, x₁, …` in order and a matrix in conjunctive normal form over literals
`w = 1` and `w ≠ 1` (words coded as lists of letters); variables not bound by the prefix are read as
`1`. This loses nothing: every first-order sentence of the language of groups is effectively
equivalent in all groups to such a code (an atomic formula `s = t` is equivalent to `s t⁻¹ = 1`) and
every code is a sentence, so decidability does not depend on the coding. Groups are taken in `Type`;
a sentence failing in some group of the variety fails in a countable elementary subgroup, which lies
in the variety.
-/

open MathlibExt.GroupTheory.PrenexSentenceShared (PrenexSentence PrenexSentence.HoldsIn)
open MathlibExt.GroupTheory.FormationVarietyPGroupsKourovka11Problem21Wanted (SatisfiesLaws)

/-- The elementary theory of the variety defined by the laws `W`: the sentences that hold in every
group of the variety. -/
def elementaryTheory (W : Set (FreeGroup ℕ)) (φ : PrenexSentence) : Prop :=
  ∀ (G : Type) [Group G], SatisfiesLaws W G → φ.HoldsIn G

/-- Kourovka 4.63 (A. Tarski): there is a non-abelian variety of groups whose elementary theory is
decidable. -/
def existsNonAbelianVarietyWithDecidableTheory : Prop :=
  ∃ W : Set (FreeGroup ℕ),
    (∃ (G : Type) (_ : Group G), SatisfiesLaws W G ∧ ∃ a b : G, a * b ≠ b * a) ∧
      ComputablePred (elementaryTheory W)

/--
Resolved false: the Kourovka Archive answers 4.63 "No", citing Zamyatin, whose theorem (the title of
the paper) is that every non-abelian variety of groups has an undecidable elementary theory; in
particular no variety containing all abelian groups and a non-abelian group has a decidable
elementary theory. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 4.63 (A. Tarski); resolution: A. P. Zamyatin, A non-Abelian variety of groups has an
undecidable elementary theory, Algebra and Logic 17 (1978), 13-17 (cited in the Archive as volume
27), Kourovka Archive, Problem 4.63: No (Zamyatin); the paper's main theorem, as its title states:
every non-abelian variety of groups has an undecidable elementary theory,
https://doi.org/10.1007/BF01670119.
-/
public theorem_wanted existsNonAbelianVarietyWithDecidableTheory_refuted :
    ¬ existsNonAbelianVarietyWithDecidableTheory

end MathlibExt.GroupTheory.NonAbelianVarietyElementaryTheoryKourovka4Problem63Wanted
