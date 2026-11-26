/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Process.ContinuousTimeMarkovChain.JumpHold

namespace MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.JumpHold

open MeasureTheory ProbabilityTheory
open MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion

/-! Checks for the countable-state jump–hold chain on `ℕ`. -/

/-- The law of the step sequence is a probability measure. -/
example (P : ℕ → PMF ℕ) : IsProbabilityMeasure (JumpHold.inputMeasure P) := inferInstance

/-- Steps that always move `n ↦ n + 1`, with every clock equal to `2`. -/
private def succSteps : ℕ → (ℕ → ℕ) × ℝ := fun _ => (Nat.succ, 2)

/-- The constant rate `4`. -/
private def rate4 : ℕ → ℝ := fun _ => 4

private theorem rate4_pos : ∀ x, 0 < rate4 x := fun _ => by norm_num [rate4]

private theorem succSteps_clock : ∀ j, 0 ≤ (succSteps j).2 := fun _ => by norm_num [succSteps]

/-- Every holding time is `2 / 4 = 1 / 2`, so the `n`-th jump time is `n / 2`. -/
private theorem jumpTime_rate4 (n : ℕ) : JumpHold.jumpTime rate4 0 succSteps n = n / 2 := by
  induction n with
  | zero => simp [JumpHold.jumpTime]
  | succ n ih =>
    rw [JumpHold.jumpTime, Finset.sum_range_succ, ← JumpHold.jumpTime, ih]
    simp only [JumpHold.holdingTime, succSteps, rate4]
    push_cast
    ring

/-- Between the first jump (time `1 / 2`) and the second (time `1`) the path is in state `1`. -/
example : JumpHold.path rate4 0 succSteps (3 / 4) = 1 := by
  have h₁ : JumpHold.jumpTime rate4 0 succSteps 1 ≤ 3 / 4 := by rw [jumpTime_rate4]; norm_num
  have h₂ : (3 / 4 : ℝ) < JumpHold.jumpTime rate4 0 succSteps (1 + 1) := by
    rw [jumpTime_rate4]; norm_num
  rw [JumpHold.path_eq_ctmcJumpChain rate4_pos succSteps_clock h₁ h₂]
  rfl

/-- After two jumps the path is in state `2`, and the state after three jumps agrees. -/
example : JumpHold.path rate4 0 succSteps (5 / 4) = 2 ∧
    JumpHold.stateAt rate4 3 0 (5 / 4) succSteps = 2 := by
  have h₁ : JumpHold.jumpTime rate4 0 succSteps 2 ≤ 5 / 4 := by rw [jumpTime_rate4]; norm_num
  have h₂ : (5 / 4 : ℝ) < JumpHold.jumpTime rate4 0 succSteps (2 + 1) := by
    rw [jumpTime_rate4]; norm_num
  refine ⟨?_, ?_⟩
  · rw [JumpHold.path_eq_ctmcJumpChain rate4_pos succSteps_clock h₁ h₂]
    rfl
  · rw [JumpHold.stateAt_eq_ctmcJumpChain rate4_pos 3 0 (5 / 4) succSteps 2 succSteps_clock
      (by norm_num) h₁ h₂]
    rfl

/-- First-step decomposition: one jump later, the jump times restart from state `1`. -/
example : JumpHold.jumpTime rate4 0 succSteps 3 =
    2 / 4 + JumpHold.jumpTime rate4 1 (ctmcShift 1 succSteps) 2 := by
  have h := JumpHold.jumpTime_succ_eq rate4 0 succSteps 2
  simpa [succSteps, rate4] using h

end MathlibExtTest.Probability.Process.ContinuousTimeMarkovChain.JumpHold
