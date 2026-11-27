/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.PenultsOfTak.FifthBound
import MathlibExt.GameTheory.PenultsOfTak.LargestPenult
import Mathlib.Tactic.Linarith

namespace MetaMathlibExt

-- The empty two-by-two penult forces the uniform constant to be at least 2/5.
example : ∃ C : ℝ, 2 / 5 ≤ C ∧ ∀ (n : ℕ) (S : Finset (Fin n × Fin n)),
    placementPenult takHasRoad S → (n : ℝ) ^ 2 / 5 - C * n ≤ S.card := by
  obtain ⟨C, hC⟩ := impartialTak_penult_card_ge_fifth
  refine ⟨C, ?_, hC⟩
  obtain ⟨S, hS, hcard⟩ := (impartialTak_isGreatest_penult_card (n := 2) (by decide)).1
  have h := hC 2 S hS
  rw [hcard] at h
  norm_num at h
  linarith

end MetaMathlibExt
