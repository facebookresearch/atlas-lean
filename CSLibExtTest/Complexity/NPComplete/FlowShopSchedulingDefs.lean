/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.FlowShopSchedulingDefs

namespace MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling

/-- Two processors and two jobs: job `0` has tasks of lengths `1, 2`, job `1` of lengths `2, 1`.
The deadline is `D`. -/
private abbrev twoJobs (D : ℕ) : FlowShopSchedulingInstance := (2, [[1, 2], [2, 1]], D)

private theorem twoJobs_four_wellFormed : WellFormed (twoJobs 4) := by
  unfold WellFormed; decide

/-- Job `0` first: processor `0` runs job `0` on `[0, 1)` and job `1` on `[1, 3)`; processor `1`
runs job `0` on `[1, 3)` and job `1` on `[3, 4)`. Every task ends by `4`. -/
private theorem twoJobs_four_feasible : FlowShopSchedulingFeasible (twoJobs 4) := by
  refine ⟨fun p j => if p.1 = 0 then (if j.1 = 0 then 0 else 1) else (if j.1 = 0 then 1 else 3),
    ?_, ?_, ?_⟩ <;> decide

/-- With the deadline `3` processor `1` is too busy: it cannot start before time `1` (the first
task of each job takes at least `1` on processor `0`) and must then run `2 + 1` units by `3`. -/
private theorem twoJobs_three_infeasible : ¬ FlowShopSchedulingFeasible (twoJobs 3) := by
  rintro ⟨σ, hend, hdisj, hord⟩
  let p0 : Fin 2 := ⟨0, by decide⟩
  let p1 : Fin 2 := ⟨1, by decide⟩
  let j0 : Fin 2 := ⟨0, by decide⟩
  let j1 : Fin 2 := ⟨1, by decide⟩
  have e10 := hend p1 j0
  have e11 := hend p1 j1
  have o0 : σ p0 j0 + 1 ≤ σ p1 j0 := hord p0 (by decide) j0
  have o1 : σ p0 j1 + 2 ≤ σ p1 j1 := hord p0 (by decide) j1
  have d := hdisj p1 j0 j1 (by decide)
  change σ p1 j0 + 2 ≤ 3 at e10
  change σ p1 j1 + 1 ≤ 3 at e11
  change σ p1 j0 + 2 ≤ σ p1 j1 ∨ σ p1 j1 + 1 ≤ σ p1 j0 at d
  omega

/-- A single job of two tasks of length `2` needs `4` time units, so the deadline `3` fails. -/
example : ¬ FlowShopSchedulingFeasible ((2, [[2, 2]], 3) : FlowShopSchedulingInstance) := by
  rintro ⟨σ, hend, -, hord⟩
  have e := hend ⟨1, by decide⟩ ⟨0, by decide⟩
  have o := hord ⟨0, by decide⟩ (by decide) ⟨0, by decide⟩
  change σ ⟨1, _⟩ ⟨0, _⟩ + 2 ≤ 3 at e
  change σ ⟨0, _⟩ ⟨0, _⟩ + 2 ≤ σ ⟨1, _⟩ ⟨0, _⟩ at o
  omega

/-- No jobs: well formed and feasible. -/
private theorem noJobs_wellFormed : WellFormed ((1, [], 1) : FlowShopSchedulingInstance) := by
  refine ⟨by decide, by decide, by decide⟩

private theorem noJobs_feasible :
    FlowShopSchedulingFeasible ((1, [], 1) : FlowShopSchedulingInstance) :=
  ⟨fun _ _ => 0, by decide, by decide, by decide⟩

/-- Malformed instances that are vacuously or trivially feasible: no processors, a job with too
few tasks (the missing task reads as length `0`), and the deadline `0` with no jobs. -/
private abbrev noProcessors : FlowShopSchedulingInstance := (0, [], 1)
private abbrev shortJob : FlowShopSchedulingInstance := (2, [[1]], 3)
private abbrev zeroDeadline : FlowShopSchedulingInstance := (1, [], 0)

private theorem malformed :
    ¬ WellFormed noProcessors ∧ ¬ WellFormed shortJob ∧ ¬ WellFormed zeroDeadline := by
  unfold WellFormed; decide

private theorem malformed_feasible :
    FlowShopSchedulingFeasible noProcessors ∧ FlowShopSchedulingFeasible shortJob ∧
      FlowShopSchedulingFeasible zeroDeadline :=
  ⟨⟨fun _ _ => 0, by decide, by decide, by decide⟩,
    ⟨fun p _ => p.1, by decide, by decide, by decide⟩,
    ⟨fun _ _ => 0, by decide, by decide, by decide⟩⟩

/-- The missing task of `shortJob` reads as length `0`. -/
example : len shortJob ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 := rfl

open MetaMathlibExt.BitstringEncoding

/-- The decision problem accepts the two jobs with the deadline `4`, and no jobs. -/
example : flowShopSchedulingDec (bitEncode (twoJobs 4)) = true := by
  simp [flowShopSchedulingDec, twoJobs_four_wellFormed, twoJobs_four_feasible]

example : flowShopSchedulingDec (bitEncode ((1, [], 1) : FlowShopSchedulingInstance)) = true := by
  simp [flowShopSchedulingDec, noJobs_wellFormed, noJobs_feasible]

/-- It rejects the well-formed two jobs with the deadline `3`. -/
example : flowShopSchedulingDec (bitEncode (twoJobs 3)) = false := by
  simp [flowShopSchedulingDec, twoJobs_three_infeasible]

/-- It rejects the feasible malformed instances. -/
example :
    flowShopSchedulingDec (bitEncode noProcessors) = false ∧
      flowShopSchedulingDec (bitEncode shortJob) = false ∧
      flowShopSchedulingDec (bitEncode zeroDeadline) = false := by
  simp [flowShopSchedulingDec, malformed.1, malformed.2.1, malformed.2.2]

example : FlowShopSchedulingFeasible noProcessors ∧ FlowShopSchedulingFeasible shortJob ∧
    FlowShopSchedulingFeasible zeroDeadline := malformed_feasible

/-- It rejects the empty bitstring, which decodes to no instance. -/
example : flowShopSchedulingDec [] = false := by
  have h : bitDecode (α := FlowShopSchedulingInstance) [] = none := rfl
  simp [flowShopSchedulingDec, h]

end MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling
