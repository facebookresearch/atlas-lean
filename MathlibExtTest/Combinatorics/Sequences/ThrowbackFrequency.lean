/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Sequences.ThrowbackFrequency

/-!
# A delayed first occurrence in a throwback sequence

Swapping the first and fifth positive integers puts the value one beyond its throwback position.
-/

namespace MetaMathlibExt.throwbackSequence_limiting_frequency_ne_zero

private def delayedMinimum (i : ℕ) : ℕ := Equiv.swap 0 4 i + 1

/-- One first leads at time five and then leads at times seven and nine. -/
example : ((Finset.range 10).filter fun k => throwbackSequence delayedMinimum k = 1) =
    {5, 7, 9} := by decide

/-- The delayed minimum has a nonzero limiting frequency. -/
example : ∃ c : ℝ, c ≠ 0 ∧ Filter.Tendsto
    (fun N : ℕ => (((Finset.range N).filter fun k =>
      throwbackSequence delayedMinimum k = 1).card : ℝ) / N) Filter.atTop (nhds c) := by
  simpa [delayedMinimum] using throwbackSequence_limiting_frequency_ne_zero delayedMinimum
    (fun _ => Nat.succ_pos _) (Nat.succ_injective.comp (Equiv.swap 0 4).injective) 4

end MetaMathlibExt.throwbackSequence_limiting_frequency_ne_zero
