/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Square relators and an undecidable word problem (Kourovka Notebook Problem 4.4)

Kourovka Notebook, Archive of Solved Problems, Problem 4.4 (S. I. Adian): construct a finitely
presented group with undecidable word problem all of whose non-trivial defining relations have the
form `A² = 1`. This problem is interesting for topologists.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import WantedExt.GroupTheory.WordProblemSolvableShared

@[expose] public section

namespace MathlibExt.GroupTheory.SquareRelatorsUnsolvableWordProblemKourovka4Problem4Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.4 (S. I.
Adian). UnsolvedMath record UM-00700215 (`KOU-4.4`), dataset ulamai/UnsolvedMath v1.8.0.

"Construct" is read as existence. A finite presentation is `⟨x₁, …, xₙ | R⟩ = F_n / ⟨⟨R⟩⟩` with `R`
a finite set of words; the word problem is the shared
`WordProblemSolvableShared.WordProblemSolvable` (decidability, `ComputablePred`, of the set of words
representing `1`), as in the Boone-Higman and Novikov entries. Every relator is the square `w²` of a
word.
-/

open MathlibExt.GroupTheory.WordProblemSolvableShared

/-- Kourovka 4.4 (S. I. Adian): there is a finitely presented group `⟨x₁, …, xₙ | R⟩` with
undecidable word problem all of whose defining relators are squares of words (relations
`A² = 1`). -/
def existsSquareRelatorPresentationUnsolvableWordProblem : Prop :=
  ∃ (n : ℕ) (R : Finset (FreeGroup (Fin n))), (∀ r ∈ R, ∃ w : FreeGroup (Fin n), r = w ^ 2) ∧
    ¬ WordProblemSolvable
        (QuotientGroup.mk' (Subgroup.normalClosure (R : Set (FreeGroup (Fin n)))))

/--
Resolved true: Sarkisyan constructed a finitely presented group with undecidable word problem whose
defining relations all have the form `A² = 1`; the Kourovka Archive answers 4.4 "It is constructed".
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.4 (S. I.
Adian); resolution: O. A. Sarkisyan, The word problem for some classes of groups and semigroups,
Candidate dissertation, Moscow University, 1983 (Russian), Kourovka Archive of Solved Problems,
Problem 4.4: It is constructed, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted existsSquareRelatorPresentationUnsolvableWordProblem_holds :
    existsSquareRelatorPresentationUnsolvableWordProblem

end MathlibExt.GroupTheory.SquareRelatorsUnsolvableWordProblemKourovka4Problem4Wanted
