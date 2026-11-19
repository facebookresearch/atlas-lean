/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.PolicyInvariance
import Mathlib.Tactic.Linarith

@[expose] public section

namespace MathlibExtTest.Economics.Macro.PolicyInvariance

open MathlibExt.Economics.Macro.PolicyInvariance

/-- Concrete Lucas example: for any nonzero money growth `m`, the two regimes give
different outcomes (`2 * m` versus `6 * m`) even though the structural parameter
`θ = 2` is the same in both. Prove via `policyOutcome_eq_reducedCoeff` and
`lucas_notInvariant`, not by unfolding the outcome in each regime separately. -/
theorem lucas_example (m : ℝ) (hm : m ≠ 0) :
    policyOutcome (2 : ℝ) ⟨1⟩ m ≠ policyOutcome (2 : ℝ) ⟨3⟩ m := by
  rw [policyOutcome_eq_reducedCoeff, policyOutcome_eq_reducedCoeff]
  obtain ⟨h1, h2, _⟩ := lucas_notInvariant
  rw [h1, h2]
  intro heq
  have : m = 0 := by linarith
  exact hm this

end MathlibExtTest.Economics.Macro.PolicyInvariance
