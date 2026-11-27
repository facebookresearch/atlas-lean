/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.WordMapsSurjectivityKourovka16Problem68

open MathlibExt.GroupTheory.WordMapsSurjectivityKourovka16Problem68Wanted

example {G : Type*} [Group G] (a b : G) :
    wordMap G (FreeGroup.of 1 * (FreeGroup.of 0)⁻¹) (a, b) = b * a⁻¹ := by
  simp [wordMap]

example {G : Type*} [Group G] (a b : G) : wordMap G 1 (a, b) = 1 := by
  simp [wordMap]

example : ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧
    ¬ Function.Surjective (wordMap (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℝ) w) := by
  simpa [psl2RealWordMapsSurjective, not_forall] using psl2RealWordMapsSurjective_refuted

example : ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧ ∃ r : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ xy, wordMap _ w xy ≠ r := by
  simpa [so3WordMapsSurjective, Function.Surjective, not_forall] using
    so3WordMapsSurjective_refuted
