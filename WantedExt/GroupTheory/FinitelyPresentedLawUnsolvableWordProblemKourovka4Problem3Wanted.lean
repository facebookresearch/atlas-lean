/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A finitely presented group with a law and insoluble word problem (Kourovka Notebook Problem 4.3)

Kourovka Notebook, Archive of Solved Problems, Problem 4.3 (S. I. Adian): construct a finitely
presented group with insoluble word problem and satisfying a non-trivial law.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import WantedExt.GroupTheory.WordProblemSolvableShared

@[expose] public section

namespace MathlibExt.GroupTheory.FinitelyPresentedLawUnsolvableWordProblemKourovka4Problem3Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.3 (S. I.
Adian). UnsolvedMath record UM-00700214 (`KOU-4.3`), dataset ulamai/UnsolvedMath v1.8.0.

"Construct" is read as existence. A finite presentation is `⟨x₁, …, xₙ | R⟩ = F_n / ⟨⟨R⟩⟩` with `R`
a finite set of words; the word problem is the shared
`WordProblemSolvableShared.WordProblemSolvable` (decidability, `ComputablePred`, of the set of words
representing `1`), as in the Boone-Higman and Novikov entries. A non-trivial law is a non-trivial
word `w` in `k` variables (`w ≠ 1` in `F_k`) that takes the value `1` under every substitution.
-/

open MathlibExt.GroupTheory.WordProblemSolvableShared

/-- Kourovka 4.3 (S. I. Adian): there is a finitely presented group
`⟨x₁, …, xₙ | R⟩ = F_n / ⟨⟨R⟩⟩` (`R` finite) with insoluble word problem satisfying a non-trivial
law: some non-trivial word `w` in `k` variables takes the value `1` under every substitution of
group elements. -/
def existsFinitelyPresentedLawUnsolvableWordProblem : Prop :=
  ∃ (n : ℕ) (R : Finset (FreeGroup (Fin n))),
    ¬ WordProblemSolvable
        (QuotientGroup.mk' (Subgroup.normalClosure (R : Set (FreeGroup (Fin n))))) ∧
      ∃ (k : ℕ) (w : FreeGroup (Fin k)), w ≠ 1 ∧
        ∀ x : Fin k → FreeGroup (Fin n) ⧸ Subgroup.normalClosure (R : Set (FreeGroup (Fin n))),
          FreeGroup.lift x w = 1

/--
Resolved true: Kharlampovich constructs a finitely presented soluble group with unsolvable word
problem; being soluble, it satisfies a non-trivial law. The Kourovka Archive answers 4.3 "This has
been done". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.3
(S. I. Adian); resolution: O. G. Kharlampovich, A finitely presented solvable group with unsolvable
word problem, Math. USSR-Izv. 19 (1982), 151-169, title and main result: a finitely presented
soluble group with unsolvable word problem; Kourovka Archive of Solved Problems, Problem 4.3: This
has been done, https://doi.org/10.1070/IM1982v019n01ABEH001405.
-/
public theorem_wanted existsFinitelyPresentedLawUnsolvableWordProblem_holds :
    existsFinitelyPresentedLawUnsolvableWordProblem

end MathlibExt.GroupTheory.FinitelyPresentedLawUnsolvableWordProblemKourovka4Problem3Wanted
