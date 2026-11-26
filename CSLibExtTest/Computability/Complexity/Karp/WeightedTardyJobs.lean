/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.Karp.WeightedTardyJobs

namespace MetaMathlibExt.Complexity.NPComplete.WeightedTardyJobs

open MetaMathlibExt (BitstringEncoding)

example : weightedTardyJobsDec ∈ ComplexityTheory.NP :=
  weightedTardyJobs_npComplete.1

example (L : ComplexityTheory.DecisionProblem) (hL : L ∈ ComplexityTheory.NP) :
    Cslib.CookLevin.PolyManyOneRed L weightedTardyJobsDec :=
  weightedTardyJobs_npComplete.2 L hL

-- A job completing on its due date is on time.
example : WeightedTardy [(3, 3, 5), (1, 3, 7)] [0, 1] = 7 := by decide

-- Equal job records still occupy separate positions in the schedule.
example : WeightedTardyJobsFeasible ([(1, 1, 7), (1, 1, 7)], 7) :=
  ⟨[0, 1], by decide, by decide⟩

-- The outer framing is valid, but the empty job payload has no processing-time block.
example : weightedTardyJobsDec (BitstringEncoding.delimit [false]) = false := rfl

-- The total natural-number decoder accepts a false-ended payload as the number two.
example : weightedTardyJobsDec
    (BitstringEncoding.delimit (BitstringEncoding.delimit [true, false, false, true, false, false]))
    = true := by
  classical
  change decide (WeightedTardyJobsFeasible ([(2, 2, 0)], 0)) = true
  rw [decide_eq_true_eq]
  exact ⟨[0], by decide, by decide⟩

-- `[false, false]` is not a canonical encoding, but it decodes to the instance `([], 2)`, whose
-- canonical encoding is `[false, false, true]`, and it is accepted.
example : BitstringEncoding.bitEncode (([], 2) : WeightedTardyJobsInstance) =
    [false, false, true] := by decide

example : weightedTardyJobsDec [false, false] = true := by
  classical
  change decide (WeightedTardyJobsFeasible ([], 2)) = true
  rw [decide_eq_true_eq]
  exact ⟨[], by decide, by decide⟩

end MetaMathlibExt.Complexity.NPComplete.WeightedTardyJobs
