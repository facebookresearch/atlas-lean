/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.MetabelianizationDecisionProblemsKourovka12Problem98

/-! Tests for the word-problem equivalence, including the full relation subgroup. -/

open MathlibExt.GroupTheory.MetabelianizationDecisionProblemsKourovka12Problem98Wanted

private theorem wordProblemTop (n : ℕ) :
    WordProblemSolvable (⊤ : Subgroup (FreeGroup (Fin n))) := by
  apply ComputablePred.computable_iff.mpr
  exact ⟨fun _ => true, Computable.const true, by funext; simp⟩

-- With all words as relations, the theorem decides the word problem of the free abelian group.
example (n : ℕ) :
    WordProblemSolvable
      ⁅(⊤ : Subgroup (FreeGroup (Fin n))), (⊤ : Subgroup (FreeGroup (Fin n)))⁆ := by
  have ht := wordProblemTop n
  have hre := ComputablePred.to_re ht
  exact (wordProblemIffMetabelianization_holds n ⊤ inferInstance hre).mp ht

-- A solver for the derived subgroup also decides the original word problem.
example {n : ℕ} (R : Subgroup (FreeGroup (Fin n))) [R.Normal] (hre : IsRecursivelyEnumerable R)
    (hd : WordProblemSolvable ⁅R, R⁆) : WordProblemSolvable R :=
  (wordProblemIffMetabelianization_holds n R inferInstance hre).mpr hd
