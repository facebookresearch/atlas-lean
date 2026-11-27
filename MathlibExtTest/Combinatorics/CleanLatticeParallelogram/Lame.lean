/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.CleanLatticeParallelogram.Lame
import Mathlib.Tactic.IntervalCases

/-! # Tests for Lamé's theorem -/

open MetaMathlibExt

-- Exact division counts as one step, even for a nonminimal pair.
example : euclidSteps 2 1 = 1 ∧ euclidSteps 4 2 = 1 := by
  simp [euclidSteps.eq_def]

-- No pair below 5 takes three steps, so the theorem singles out the divisor 3.
example {v : ℕ} (hv : 0 < v) (hv5 : v < 5) : euclidSteps 5 v = 3 ↔ v = 3 := by
  constructor
  · intro hsteps
    have hmin (a b : ℕ) (hba : b < a) (hb : 0 < b) (hs : euclidSteps a b = 3) : 5 ≤ a := by
      by_contra! ha
      interval_cases a <;> interval_cases b <;> simp [euclidSteps.eq_def] at hs
    exact (lame_euclidSteps_minimal (by decide : 1 ≤ 3) hv5 hv hsteps hmin).2
  · rintro rfl
    simp [euclidSteps.eq_def]
