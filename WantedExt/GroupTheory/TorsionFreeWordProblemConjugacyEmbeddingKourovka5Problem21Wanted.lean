/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Solvable word problem versus solvable conjugacy problem (Kourovka Notebook Problem 5.21)

Kourovka Notebook, Archive of Solved Problems, Problem 5.21 (D. J. Collins): can every torsion-free
group with solvable word problem be embedded in a group with solvable conjugacy problem?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement
public import WantedExt.GroupTheory.MetabelianizationDecisionProblemsKourovka12Problem98Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.TorsionFreeWordProblemConjugacyEmbeddingKourovka5Problem21Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.21 (D. J.
Collins). UnsolvedMath record UM-00700305 (`KOU-5.21`), dataset ulamai/UnsolvedMath v1.8.0.

Groups are finitely generated, the setting in which the word and conjugacy problems are defined and
the setting of Darbinyan's theorem. A finitely generated group is written `F ⧸ N` for a normal
subgroup `N` of a free group `F` of finite rank; its word problem is solvable when membership of
words (lists of letters) in `N` is computable, and its conjugacy problem is solvable when conjugacy
of pairs of words modulo `N` is computable (`WordProblemSolvable` and `ConjugacyProblemSolvable` of
the Kourovka 12.98 entry, reused here). Both notions do not depend on the finite generating set.
Torsion-free: no non-trivial element of finite order.
-/

open MathlibExt.GroupTheory.MetabelianizationDecisionProblemsKourovka12Problem98Wanted
  (WordProblemSolvable ConjugacyProblemSolvable)

/-- Kourovka 5.21 (D. J. Collins): every finitely generated torsion-free group with solvable word
problem embeds in a finitely generated group with solvable conjugacy problem. Finitely generated
groups are written `F ⧸ N` for a normal subgroup `N` of a free group `F` of finite rank. -/
def torsionFreeSolvableWordProblemEmbeds : Prop :=
  ∀ (n : ℕ) (M : Subgroup (FreeGroup (Fin n))) [M.Normal],
    (∀ g : FreeGroup (Fin n) ⧸ M, g ≠ 1 → ¬ IsOfFinOrder g) → WordProblemSolvable M →
      ∃ (m : ℕ) (N : Subgroup (FreeGroup (Fin m))) (_ : N.Normal), ConjugacyProblemSolvable N ∧
        ∃ f : FreeGroup (Fin n) ⧸ M →* FreeGroup (Fin m) ⧸ N, Function.Injective f

/--
Resolved false: Darbinyan (Invent. Math. 224 (2021), 987-997, abstract) shows that there are
finitely presented torsion-free groups with decidable word problem that embed in no finitely
generated group with decidable conjugacy problem; the Kourovka Archive answers 5.21 "No, not every".
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.21 (D. J.
Collins); resolution: A. Darbinyan, Groups with decidable word problem that do not embed in groups
with decidable conjugacy problem, Invent. Math. 224 (2021), 987-997, abstract: there exist finitely
presented torsion-free groups with decidable word problem that cannot be embedded in any finitely
generated group with decidable conjugacy problem, answering Collins' question; Kourovka Archive,
Problem 5.21: No, not every, https://doi.org/10.1007/s00222-020-01022-0.
-/
public theorem_wanted torsionFreeSolvableWordProblemEmbeds_refuted :
    ¬ torsionFreeSolvableWordProblemEmbeds

end MathlibExt.GroupTheory.TorsionFreeWordProblemConjugacyEmbeddingKourovka5Problem21Wanted
