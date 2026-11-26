/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.JobShopSchedulingDefs

namespace MetaMathlibExt.Complexity.NPComplete.JobShopScheduling

/-- Two processors and two jobs: job `0` runs `3` units on processor `1`, then `2` units on
processor `2`; job `1` runs `2` units on processor `2`, then `4` units on processor `1`. -/
private abbrev twoJobs (D : ℕ) : JobShopSchedulingInstance :=
  (2, [[(3, 1), (2, 2)], [(2, 2), (4, 1)]], D)

/-- Start times given job by job, in the order of each job's tasks. -/
private def startsOf (s : List (List ℕ)) (i : JobShopSchedulingInstance) (t : Task i) : ℕ :=
  (s.getD t.1 []).getD t.2 0

/-- The accessors read the length and the processor of a task. -/
example :
    taskLength (twoJobs 7) ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩ = 4 ∧
      taskProcessor (twoJobs 7) ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩ = 1 ∧
      taskLength (twoJobs 7) ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩ = 2 ∧
      taskProcessor (twoJobs 7) ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩ = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The two-job instance is well formed. -/
example : WellFormed (twoJobs 7) := by unfold WellFormed; decide

/-- A processor may recur in a job when no two consecutive tasks use it. -/
example : WellFormed (2, [[(1, 1), (1, 2), (1, 1)]], 5) := by unfold WellFormed; decide

/-- Malformed: no processors. -/
example : ¬ WellFormed (0, [], 1) := by unfold WellFormed; decide

/-- Malformed: a job with no tasks. -/
example : ¬ WellFormed (1, [[(1, 1)], []], 1) := by unfold WellFormed; decide

/-- Malformed: processor `0` is outside `{1, …, m}`. -/
example : ¬ WellFormed (1, [[(1, 0)]], 1) := by unfold WellFormed; decide

/-- Malformed: processor `2` is outside `{1}`. -/
example : ¬ WellFormed (1, [[(1, 2)]], 1) := by unfold WellFormed; decide

/-- Malformed: two consecutive tasks of a job on the same processor. -/
example : ¬ WellFormed (2, [[(1, 1), (1, 1)]], 5) := by unfold WellFormed; decide

/-- Malformed: deadline `0`. -/
example : ¬ WellFormed (1, [[(1, 1)]], 0) := by unfold WellFormed; decide

/-- An interleaved schedule meets the deadline `7`: processor `1` runs job `0`'s first task on
`[0, 3)` and job `1`'s second task on `[3, 7)`; processor `2` runs job `1`'s first task on
`[0, 2)` and job `0`'s second task on `[3, 5)`. -/
private theorem twoJobs_seven_feasible : JobShopSchedulingFeasible (twoJobs 7) :=
  ⟨startsOf [[0, 3], [0, 3]] (twoJobs 7), by decide, by decide, by decide, by decide⟩

/-- Each job alone fits in `6` units (job `0` needs `5`, job `1` needs `6`), but processor `1`
carries `3 + 4 = 7` units of work, so no schedule meets the deadline `6`. -/
private theorem twoJobs_six_infeasible : ¬ JobShopSchedulingFeasible (twoJobs 6) := by
  rintro ⟨σ, -, hp, hc, hd⟩
  have a := hc ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ rfl
  have b := hc ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ rfl
  have c := hd ⟨0, by decide⟩ ⟨1, by decide⟩ rfl
  have d := hd ⟨1, by decide⟩ ⟨1, by decide⟩ rfl
  have e := hp ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩ rfl
  have f := hp ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩ ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ rfl
  change σ ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ + 3 ≤ σ ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩ at a
  change σ ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩ + 2 ≤ σ ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩ at b
  change σ ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩ + 2 ≤ 6 at c
  change σ ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩ + 4 ≤ 6 at d
  change σ ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩ < σ ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ →
    σ ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩ + 4 ≤ σ ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ at e
  change σ ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ < σ ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩ →
    σ ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ + 3 ≤ σ ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩ at f
  omega

/-- The job order alone can rule out a deadline: one job of lengths `3` and `2` on different
processors needs `5` units. -/
example : ¬ JobShopSchedulingFeasible (2, [[(3, 1), (2, 2)]], 4) := by
  rintro ⟨σ, -, -, hc, hd⟩
  have a := hc ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ rfl
  have c := hd ⟨0, by decide⟩ ⟨1, by decide⟩ rfl
  change σ ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ + 3 ≤ σ ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩ at a
  change σ ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩ + 2 ≤ 4 at c
  omega

/-- Start times are one-to-one on each processor even for tasks of length `0`: two such tasks
on one processor may not share a start time. -/
example :
    ¬ (∀ t t' : Task (1, [[(0, 1)], [(0, 1)]], 1),
      taskProcessor _ t = taskProcessor _ t' →
        startsOf [[0], [0]] _ t = startsOf [[0], [0]] _ t' → t = t') := by
  decide

/-- The same two tasks may start at `0` and `1`, and both end by the deadline `1`. -/
example : JobShopSchedulingFeasible (1, [[(0, 1)], [(0, 1)]], 1) :=
  ⟨startsOf [[0], [1]] _, by decide, by decide, by decide, by decide⟩

open MetaMathlibExt.BitstringEncoding in
/-- The decision problem accepts the encoding of the feasible instance. -/
example : jobShopSchedulingDec (bitEncode (twoJobs 7)) = true := by
  have hw : WellFormed (twoJobs 7) := by unfold WellFormed; decide
  simp [jobShopSchedulingDec, hw, twoJobs_seven_feasible]

open MetaMathlibExt.BitstringEncoding in
/-- It rejects the encoding of the well-formed instance whose deadline no schedule meets. -/
example : jobShopSchedulingDec (bitEncode (twoJobs 6)) = false := by
  simp [jobShopSchedulingDec, twoJobs_six_infeasible]

open MetaMathlibExt.BitstringEncoding in
/-- It rejects the encoding of a malformed instance even when a schedule exists: two
consecutive tasks of a job on one processor. -/
example :
    jobShopSchedulingDec
      (bitEncode ((2, [[(1, 1), (1, 1)]], 5) : JobShopSchedulingInstance)) = false := by
  have hw : ¬ WellFormed (2, [[(1, 1), (1, 1)]], 5) := by unfold WellFormed; decide
  simp [jobShopSchedulingDec, hw]

/-- It rejects the empty bitstring, which decodes to no instance. -/
example : jobShopSchedulingDec [] = false := by
  have h : MetaMathlibExt.BitstringEncoding.bitDecode (α := JobShopSchedulingInstance) [] =
      none :=
    rfl
  simp [jobShopSchedulingDec, h]

end MetaMathlibExt.Complexity.NPComplete.JobShopScheduling
