/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FreeGroupLogIndexSeparationKourovka15Problem35

open MathlibExt.GroupTheory.FreeGroupLogIndexSeparationKourovka15Problem35Wanted

-- At the minimum rank, a single word defeats all candidate separating subgroups.
example (C : ℝ) : ∃ w : FreeGroup (Fin 2), 1 < w.norm ∧
    ∀ H : Subgroup (FreeGroup (Fin 2)), H.FiniteIndex → w ∉ H →
      C * Real.log w.norm < (H.index : ℝ) := by
  by_contra! h
  exact logIndexSeparation_refuted ⟨2, le_rfl, C, h⟩

-- Infinite-index subgroups would invalidate the conclusion because their index is coded as zero.
example (w : FreeGroup (Fin 2)) (hw : 1 < w.norm) :
    w ∉ (⊥ : Subgroup (FreeGroup (Fin 2))) ∧ (⊥ : Subgroup (FreeGroup (Fin 2))).index = 0 := by
  let : Infinite (FreeGroup (Fin 2)) := Infinite.of_surjective _ FreeGroup.norm_surjective
  constructor
  · intro h
    rw [Subgroup.mem_bot.mp h, FreeGroup.norm_one] at hw
    omega
  · simp [Subgroup.index_bot]
