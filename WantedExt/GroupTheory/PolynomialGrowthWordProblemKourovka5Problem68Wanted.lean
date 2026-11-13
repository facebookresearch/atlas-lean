/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Word problem for finitely presented groups of polynomial growth (Kourovka Notebook Problem 5.68)

Kourovka Notebook, Archive of Solved Problems, Problem 5.68 (P. E. Schupp): let G be a
finitely-presented group, and assume that G has polynomial growth in the sense of Milnor. Show that
G has soluble word problem.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FinitelyPresentedGroup
public import MathlibExt.GroupTheory.GroupGrowth
public import WantedExt.GroupTheory.WordProblemSolvableShared

@[expose] public section

namespace MathlibExt.GroupTheory.PolynomialGrowthWordProblemKourovka5Problem68Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.68 (P. E.
Schupp). UnsolvedMath record UM-00700346 (`KOU-5.68`), dataset ulamai/UnsolvedMath v1.8.0.

A finite presentation is a surjection `φ : FreeGroup (Fin n) →* G` whose kernel is the normal
closure of a finite set (Mathlib's `IsFinitelyNormallyGenerated`). Polynomial growth is
`Group.Generators.HasPolynomialGrowth` of `MathlibExt.GroupTheory.GroupGrowth` for some finite
generating family; soluble word problem is the shared `WordProblemSolvable φ`. The conclusion is
asserted for every finite presentation.
-/

open MathlibExt.GroupTheory.WordProblemSolvableShared (WordProblemSolvable)

/-- Kourovka 5.68 (P. E. Schupp): a finitely presented group of polynomial growth (with respect to
some finite generating family) has soluble word problem with respect to every finite
presentation. -/
def polynomialGrowthWordProblemSolvable : Prop :=
  ∀ (G : Type) [Group G] (n : ℕ) (φ : FreeGroup (Fin n) →* G), Function.Surjective φ →
    φ.ker.IsFinitelyNormallyGenerated →
    (∃ (m : ℕ) (P : Group.Generators G (Fin m)), P.HasPolynomialGrowth) →
    WordProblemSolvable φ

/--
Resolved true: the Kourovka Archive records 5.68 as shown by Gromov (1981), whose theorem makes a
finitely generated group of polynomial growth virtually nilpotent (the statement of
`GromovPolynomialGrowthWanted`); finitely presented groups of polynomial growth therefore have
soluble word problem with respect to every finite presentation. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.68 (P. E. Schupp); resolution: M.
Gromov, Groups of polynomial growth and expanding maps, Publ. Math. IHES 53 (1981), 53-73, Kourovka
Archive, Problem 5.68: This has been shown (Gromov), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted polynomialGrowthWordProblemSolvable_holds :
    polynomialGrowthWordProblemSolvable

end MathlibExt.GroupTheory.PolynomialGrowthWordProblemKourovka5Problem68Wanted
