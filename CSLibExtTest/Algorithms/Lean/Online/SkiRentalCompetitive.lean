/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import CSLibExt.Algorithms.Lean.Online.SkiRentalCompetitive
import Mathlib.Tactic

@[expose] public section

namespace Cslib.Algorithms.Lean.Online.CompetitiveFramework

open SkiRental

/-- At `B = 3`, break-even is `(5 / 3, 0)`-competitive. -/
example : Competitive (skiProblem 3) (skiStrategy (SkiRental.breakEven 3))
    (5 / 3) 0 := by
  have h := breakEven_competitive (B := 3) (by decide)
  have hEq : ((5 : ℝ) / 3) = ((2 * ((3 : ℕ) : ℝ) - 1) / ((3 : ℕ) : ℝ)) := by
    norm_num
  rw [hEq]
  exact h

/-- At `B = 3`, break-even is `(0, 5)`-competitive. -/
example : Competitive (skiProblem 3) (skiStrategy (SkiRental.breakEven 3))
    0 5 := by
  have h := breakEven_additive_zero (B := 3) (by decide)
  have hEq : (5 : ℝ) = 2 * ((3 : ℕ) : ℝ) - 1 := by norm_num
  rw [hEq]
  exact h

/-- At `B = 3`, the strict lower bound `5 / 3` is witnessed against
break-even at `c = 3 / 2`, with computed native costs. -/
example : ∃ σ : List Unit, (skiProblem 3).legal σ ∧
    ENNReal.ofReal (3 / 2) * ENNReal.ofReal (SkiRental.opt 3 σ.length : ℝ)
      < ENNReal.ofReal
        (SkiRental.cost 3 (SkiRental.breakEven 3) σ.length : ℝ) := by
  have hLB := ski_strictLowerBound (B := 3) (by decide)
  have hA := skiStrategy_feasible 3 (SkiRental.breakEven 3)
  have hc : (3 : ℝ) / 2 < ((2 * ((3 : ℕ) : ℝ) - 1) / ((3 : ℕ) : ℝ)) := by
    norm_num
  obtain ⟨σ, hσ, hlt⟩ := hLB (skiStrategy (SkiRental.breakEven 3)) hA
    (3 / 2) (by norm_num) hc
  refine ⟨σ, hσ, ?_⟩
  rw [ski_optCost, algCost_skiStrategy] at hlt
  exact hlt

end Cslib.Algorithms.Lean.Online.CompetitiveFramework
