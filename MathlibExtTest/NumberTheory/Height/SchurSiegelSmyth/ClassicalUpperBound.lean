/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Height.SchurSiegelSmyth.ClassicalUpperBound

/-!
# Finiteness of the Schur–Siegel–Smyth trace constant
-/

open MathlibExt.NumberTheory.SchurSiegelSmyth

/-- The extended-real supremum is represented by a real number in the closed interval `[0, 2]`. -/
example : ∃ c ∈ Set.Icc (0 : ℝ) 2, (c : EReal) = schurSiegelSmythConstant := by
  have htop := ne_top_of_le_ne_top (EReal.coe_ne_top 2) classicalUpperBound_wanted
  have hbot := ne_bot_of_le_ne_bot EReal.zero_ne_bot zero_le_schurSiegelSmythConstant
  have h := EReal.coe_toReal htop hbot
  refine ⟨_, ⟨EReal.coe_le_coe_iff.mp ?_, EReal.coe_le_coe_iff.mp ?_⟩, h⟩
  · rw [h]
    exact zero_le_schurSiegelSmythConstant
  · rw [h]
    exact classicalUpperBound_wanted
