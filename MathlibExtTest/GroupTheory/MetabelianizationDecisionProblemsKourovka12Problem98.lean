/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.MetabelianizationDecisionProblemsKourovka12Problem98

/-! Tests for the word-problem equivalence, the rank-zero case and the conjugacy predicate. -/

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

-- In rank zero the only word is empty and hence belongs to the derived subgroup.
example : WordProblemSolvable (⊥ : Subgroup (FreeGroup (Fin 0))) := by
  have hre : IsRecursivelyEnumerable (⊥ : Subgroup (FreeGroup (Fin 0))) := by
    rw [Subsingleton.elim (⊥ : Subgroup (FreeGroup (Fin 0))) ⊤]
    exact ComputablePred.to_re (wordProblemTop 0)
  apply (wordProblemIffMetabelianization_holds 0 ⊥ inferInstance hre).mpr
  apply ComputablePred.computable_iff.mpr
  refine ⟨fun _ => true, Computable.const true, ?_⟩
  funext w
  rw [Subsingleton.elim w []]
  simp [← FreeGroup.one_eq_mk]

-- In the trivial quotient every pair is conjugate, with the identity as a witness.
example (n : ℕ) : ConjugacyProblemSolvable (⊤ : Subgroup (FreeGroup (Fin n))) := by
  apply ComputablePred.computable_iff.mpr
  refine ⟨fun _ => true, Computable.const true, ?_⟩
  funext wv
  simp
