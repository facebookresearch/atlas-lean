/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.GroupTheory.WordProblemSolvableShared

open MathlibExt.GroupTheory.WordProblemSolvableShared

-- With no generators, the empty word is the only input.
example {G : Type*} [Group G] (φ : FreeGroup (Fin 0) →* G) : WordProblemSolvable φ := by
  refine ComputablePred.computable_iff.mpr ⟨fun _ => true, Computable.const true, ?_⟩
  funext w
  have hw : w = [] := by
    cases w with
    | nil => rfl
    | cons a _ => exact Fin.elim0 a.1
  simp [hw, ← FreeGroup.one_eq_mk]
