/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Sort.QuickExpectedRecurrence

namespace Cslib.Algorithms.Lean.TimeM

/-- Boundary check: `E 2 = 1` by the closed form (the value that
refuted the earlier draft closed form), and `E 0 = 0`. -/
example : qsExpected 0 = 0 ∧ qsExpected 2 = 1 :=
  ⟨rfl, by norm_num [qsExpected, qsPair]⟩

/-- The link at `n = 3`: the formal expectation of `quickSort` on a random
ordering of `[30, 10, 20]` is `qsExpected 3`, evaluated here from the
recurrence. `QuickExpectedTests` gets the same `8 / 3` from the pair sum. -/
example : (expectedTime (quickSort (α := ℕ))
    (uniformPermutation [30, 10, 20])).toReal = 8 / 3 := by
  rw [quickSort_expectedTime_uniformPermutation_eq_qsExpected _ (by decide)]
  norm_num [qsExpected, qsPair]

/-- The closed form at `n = 4`: `2 * 5 * H 4 - 4 * 4 = 29 / 6`, the value
`QuickExpectedTests` gets from the pair sum. -/
example : (expectedTime (quickSort (α := ℕ))
    (uniformPermutation [4, 1, 3, 2])).toReal = 29 / 6 := by
  rw [quickSort_expectedTime_uniformPermutation_eq_harmonic _ (by decide)]
  norm_num [harmonic, Finset.sum_range_succ]

/-- The recurrence gives the same value at `n = 4`. -/
example : qsExpected 4 = 29 / 6 := by
  norm_num [qsExpected, qsPair]

#print axioms quickSort_expectedTime_uniformPermutation_eq_harmonic
#print axioms quickSort_expectedTime_uniformPermutation_eq_qsExpected

end Cslib.Algorithms.Lean.TimeM
