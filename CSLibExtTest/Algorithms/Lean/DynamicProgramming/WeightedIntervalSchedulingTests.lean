/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.WeightedIntervalScheduling
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.WeightedIntervalScheduling

/-- Boundary check: the optimum of the empty family is `0`. -/
example : wisOpt (![0, 1] : Fin 2 → ℕ) ![2, 3] ![3, 5] ∅ = 0 := by
  decide

/-- Overlapping intervals `[0, 2)` (weight `3`) and `[1, 3)` (weight `5`): only one fits, so
the optimum is the larger weight. -/
example : wisOpt (![0, 1] : Fin 2 → ℕ) ![2, 3] ![3, 5] {0, 1} = 5 := by
  decide

/-- The same check with the larger weight on the first interval. -/
example : wisOpt (![0, 1] : Fin 2 → ℕ) ![2, 3] ![5, 3] {0, 1} = 5 := by
  decide

/-- Endpoint-touching intervals `[0, 1)` and `[1, 2)` are compatible: the optimum sums both
weights. -/
example : wisOpt (![0, 1] : Fin 2 → ℕ) ![1, 2] ![3, 5] {0, 1} = 8 := by
  decide

/-- Disjoint intervals `[0, 1)` and `[2, 3)`: the optimum sums both weights. -/
example : wisOpt (![0, 2] : Fin 2 → ℕ) ![1, 3] ![3, 5] {0, 1} = 8 := by
  decide

/-- The exchange identity on the overlapping pair: adjoining `[0, 2)` (weight `3`) to
`{[1, 3)}` (weight `5`) leaves no compatible interval, so the optimum is `max 5 (3 + 0)`. -/
example :
    wisOpt (![0, 1] : Fin 2 → ℕ) ![2, 3] ![3, 5] (insert 0 {1}) =
      max (wisOpt (![0, 1] : Fin 2 → ℕ) ![2, 3] ![3, 5] {1})
        (3 + wisOpt (![0, 1] : Fin 2 → ℕ) ![2, 3] ![3, 5]
          (({1} : Finset (Fin 2)).filter
            (Cslib.Algorithms.Lean.TimeM.IntervalCompatible (![0, 1] : Fin 2 → ℕ) ![2, 3] 0))) :=
  wisOpt_insert _ _ _ 0 {1} (by decide)

end Cslib.Algorithms.Lean.WeightedIntervalScheduling
