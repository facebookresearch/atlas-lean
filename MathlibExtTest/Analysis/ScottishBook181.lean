/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ScottishBook181

/-! # Convergence of the integer translates in Steinhaus's periodization problem -/

open MathlibExt.Analysis.ScottishBook181Wanted

-- The nonzero value of the periodization guarantees convergence at every real shift.
example : ∃ f : ℝ → ℝ, Continuous f ∧ (∀ x, 0 < f x) ∧
    ∀ x, HasSum (fun n : ℤ ↦ f (x + n)) 1 := by
  obtain ⟨f, hcont, hpos, hsum⟩ := steinhaus181_periodization_one
  refine ⟨f, hcont, hpos, fun x ↦ ?_⟩
  have hs : Summable (fun n : ℤ ↦ f (x + n)) := by
    by_contra h
    exact one_ne_zero ((hsum x).symm.trans (tsum_eq_zero_of_not_summable h))
  simpa only [hsum] using hs.hasSum
