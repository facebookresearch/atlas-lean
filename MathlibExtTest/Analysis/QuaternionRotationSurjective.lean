/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.QuaternionRotationSurjective

-- Tests for the surjectivity of the unit-quaternion rotation action: a
-- preimage of `diag(1, -1, -1)` (the `n 2 = -1` alignment branch), a preimage
-- of the identity, and column alignment at `![0, 0, -1]`.

open Quaternion QuaternionRotation

example : ∃ u : unitary ℍ, rotMatrix (u : ℍ) = !![1, 0, 0; 0, -1, 0; 0, 0, -1] := by
  have hmem : !![1, 0, 0; 0, -1, 0; 0, 0, -1] ∈
      Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    rw [Matrix.mem_specialOrthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_orthogonalGroup_iff']
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
    · simp [Matrix.det_fin_three]
  obtain ⟨u, hu⟩ := unitaryHomSpecialOrthogonalGroup_surjective ⟨_, hmem⟩
  exact ⟨u, Subtype.ext_iff.mp hu⟩

example : ∃ u : unitary ℍ, rotMatrix (u : ℍ) = 1 := by
  obtain ⟨u, hu⟩ := unitaryHomSpecialOrthogonalGroup_surjective 1
  exact ⟨u, Subtype.ext_iff.mp hu⟩

example : ∃ u : unitary ℍ, ∀ i, rotMatrix (u : ℍ) i 2 = ![0, 0, -1] i := by
  have hn : (![0, 0, -1] : Fin 3 → ℝ) 0 ^ 2 + (![0, 0, -1] : Fin 3 → ℝ) 1 ^ 2 +
      (![0, 0, -1] : Fin 3 → ℝ) 2 ^ 2 = 1 := by simp
  exact exists_rotMatrix_apply_two _ hn
