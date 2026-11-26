/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SolubleRightOrderableWordProblemKourovka17Problem28

open MathlibExt.GroupTheory.SolubleRightOrderableWordProblemKourovka17Problem28Wanted
open MathlibExt.GroupTheory.WordProblemSolvableShared

-- With no generators, every input word is empty, so its identity predicate is computable.
private theorem emptyAlphabet {G : Type} [Group G] (gens : Fin 0 → G) :
    WordProblemSolvable (FreeGroup.lift gens) := by
  have h : ComputablePred (fun _ : List (Fin 0 × Bool) => True) :=
    ComputablePred.computable_iff.mpr ⟨fun _ => true, Computable.const _, by simp⟩
  apply h.of_eq
  intro w
  cases w with
  | nil => simp
  | cons c _ => exact Fin.elim0 c.1

-- The witness supplies a nonempty finite alphabet for both computability assertions.
example : ∃ (G : Type) (_ : Group G) (k : ℕ) (gens : Fin k → G),
    0 < k ∧ IsRecursivelyPresented (FreeGroup.lift gens) ∧
      ¬ WordProblemSolvable (FreeGroup.lift gens) := by
  obtain ⟨G, inst, _, _, k, gens, _, hRE, hWP⟩ := solubleRightOrderableInsolubleWordProblem_holds
  refine ⟨G, inst, k, gens, Nat.pos_of_ne_zero ?_, hRE, hWP⟩
  rintro rfl
  exact hWP (emptyAlphabet gens)
