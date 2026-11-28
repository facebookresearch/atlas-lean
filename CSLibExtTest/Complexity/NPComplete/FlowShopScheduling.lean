/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.FlowShopScheduling
import CSLibExt.Complexity.NPComplete.FlowShopScheduling.Hardness
import CSLibExt.Complexity.NPComplete.FlowShopScheduling.Membership
meta import CSLibExt.Complexity.NPComplete.FlowShopScheduling.Membership
meta import MathlibExt.Computability.BinaryNatEncoding

/-! # Tests for the NP-completeness of FLOW-SHOP SCHEDULING -/

namespace MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode delimit)

-- The original statement, with its exact type.
example :
    flowShopSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L flowShopSchedulingDec :=
  flowShopScheduling_npComplete

example : flowShopSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP :=
  flowShopScheduling_mem_NP

example (L : MetaMathlibExt.ComplexityTheory.DecisionProblem)
    (hL : L ∈ MetaMathlibExt.ComplexityTheory.NP) :
    Cslib.CookLevin.PolyManyOneRed L flowShopSchedulingDec :=
  flowShopScheduling_npHard L hL

example (x : List Bool) : flowShopSchedulingDec x = true ↔
    ∃ w : List Bool, w.length ≤ 3 * x.length * (2 * x.length + 1) ∧
      Verification.check x w = true :=
  Verification.dec_iff_check x

example : MetaMathlibExt.ComplexityTheory.IsPolyTime
    (fun q : List Bool × List Bool => Verification.check q.1 q.2) :=
  Verification.isPolyTime_check

/-! ### The verifier on encoded schedules -/

/-- Two processors and two jobs, of task lengths `1, 2` and `2, 1`, with the deadline `D`. -/
private def twoJobs (D : ℕ) : FlowShopSchedulingInstance := (2, [[1, 2], [2, 1]], D)

/-- Job `0` runs on `[0, 1)` and `[1, 3)`, job `1` on `[1, 3)` and `[3, 4)`. -/
private def goodSched : List (List ℕ) := [[0, 1], [1, 3]]

-- The schedule meets the deadline `4`.
#guard Verification.check (bitEncode (twoJobs 4)) (bitEncode goodSched)
-- With the deadline `3` the last task, ending at `4`, is late.
#guard !Verification.check (bitEncode (twoJobs 3)) (bitEncode goodSched)
-- Both jobs start on processor `0` at time `0`: they overlap.
#guard !Verification.check (bitEncode (twoJobs 4)) (bitEncode ([[0, 1], [0, 3]] : List (List ℕ)))
-- Job `0` starts on processor `1` before its task on processor `0` ends.
#guard !Verification.check (bitEncode (twoJobs 9)) (bitEncode ([[0, 0], [1, 3]] : List (List ℕ)))
-- A schedule row with three start times, one with one, a missing row and an extra row.
#guard !Verification.check (bitEncode (twoJobs 9))
  (bitEncode ([[0, 1, 2], [1, 3]] : List (List ℕ)))
#guard !Verification.check (bitEncode (twoJobs 9)) (bitEncode ([[0], [1, 3]] : List (List ℕ)))
#guard !Verification.check (bitEncode (twoJobs 9)) (bitEncode ([[0, 1]] : List (List ℕ)))
#guard !Verification.check (bitEncode (twoJobs 9))
  (bitEncode ([[0, 1], [1, 3], [5, 6]] : List (List ℕ)))
-- An undecodable certificate.
#guard !Verification.check (bitEncode (twoJobs 4)) [true]
-- Malformed instances: an undecodable bitstring, no processors, and a job with one task.
#guard !Verification.check [true] []
#guard !Verification.check (bitEncode ((0, [], 1) : FlowShopSchedulingInstance)) []
#guard !Verification.check (bitEncode ((2, [[1]], 9) : FlowShopSchedulingInstance))
  (bitEncode ([[0, 1]] : List (List ℕ)))
-- The deadline `0` is malformed, even for all-zero tasks that it would accommodate.
#guard !Verification.check (bitEncode ((1, [], 0) : FlowShopSchedulingInstance)) []
#guard !Verification.check (bitEncode ((3, [[0, 0, 0]], 0) : FlowShopSchedulingInstance))
  (bitEncode ([[0, 0, 0]] : List (List ℕ)))
-- With the deadline `1` the same all-zero job is scheduled.
#guard Verification.check (bitEncode ((3, [[0, 0, 0]], 1) : FlowShopSchedulingInstance))
  (bitEncode ([[0, 0, 0]] : List (List ℕ)))
-- No jobs: only the empty schedule is accepted.
#guard Verification.check (bitEncode ((2, [], 1) : FlowShopSchedulingInstance)) []
#guard !Verification.check (bitEncode ((2, [], 1) : FlowShopSchedulingInstance))
  (bitEncode ([[0, 0]] : List (List ℕ)))

/-! ### Proved instances of the decision problem -/

/-- Rejecting every certificate rules the bitstring out of the language. -/
private theorem dec_false_of_check_false {x : List Bool}
    (h : ∀ w, Verification.check x w = false) : flowShopSchedulingDec x = false := by
  cases hx : flowShopSchedulingDec x
  · rfl
  · obtain ⟨w, -, hw⟩ := (Verification.dec_iff_check x).mp hx
    rw [h w] at hw
    cases hw

example : flowShopSchedulingDec [true] = false :=
  dec_false_of_check_false fun _ => rfl

/-- `m` is framed as the noncanonical block `[false]` (it decodes to `2`) and `D` as the
noncanonical suffix `[true, true, false, false]` (it decodes to `19`). -/
private def xNC : List Bool :=
  delimit [false] ++ delimit (bitEncode ([[1, 2], [2, 1]] : List (List ℕ))) ++
    [true, true, false, false]

private theorem decode_xNC :
    bitDecode (α := FlowShopSchedulingInstance) xNC = some (2, [[1, 2], [2, 1]], 19) := rfl

private theorem check_xNC : Verification.check xNC (bitEncode goodSched) = true := by
  rw [Verification.check_iff]
  exact ⟨2, [[1, 2], [2, 1]], 19, goodSched, decode_xNC, bitDecode_bitEncode _, by decide,
    by decide, by decide⟩

example : flowShopSchedulingDec xNC = true :=
  (Verification.dec_iff_check xNC).mpr ⟨_, by decide, check_xNC⟩

/-- A job with one task on two processors is rejected under every certificate. -/
private def xArity : List Bool := bitEncode ((2, [[1]], 4) : FlowShopSchedulingInstance)

private theorem check_xArity (w : List Bool) : Verification.check xArity w = false := by
  cases h : Verification.check xArity w
  · rfl
  · rw [Verification.check_iff] at h
    obtain ⟨m, jobs, D, sched, hd, -, -, -, ho⟩ := h
    rw [show xArity = bitEncode ((2, [[1]], 4) : FlowShopSchedulingInstance) from rfl,
      bitDecode_bitEncode] at hd
    obtain ⟨rfl, rfl, rfl⟩ := by simpa using hd
    rw [Verification.outerD_iff] at ho
    have := (Verification.localD_iff _ _ _ _ _).mp (ho.2.1 0 (by decide))
    simp at this

example : flowShopSchedulingDec xArity = false := dec_false_of_check_false check_xArity

/-- The deadline `0` is rejected under every certificate, although the instance has no jobs. -/
private def xZeroDeadline : List Bool :=
  bitEncode ((1, ([] : List (List ℕ)), 0) : FlowShopSchedulingInstance)

private theorem check_xZeroDeadline (w : List Bool) :
    Verification.check xZeroDeadline w = false := by
  cases h : Verification.check xZeroDeadline w
  · rfl
  · rw [Verification.check_iff] at h
    obtain ⟨m, jobs, D, sched, hd, -, -, hD, -⟩ := h
    rw [show xZeroDeadline = bitEncode ((1, ([] : List (List ℕ)), 0) :
      FlowShopSchedulingInstance) from rfl, bitDecode_bitEncode] at hd
    obtain ⟨rfl, rfl, rfl⟩ := by simpa using hd
    cases hD

example : flowShopSchedulingDec xZeroDeadline = false :=
  dec_false_of_check_false check_xZeroDeadline

/-- With no jobs, the verifier reads `m` but never iterates over the processors: `m = 2⁶⁴` is
accepted with the empty schedule. -/
private def xHuge : List Bool :=
  bitEncode ((2 ^ 64, ([] : List (List ℕ)), 1) : FlowShopSchedulingInstance)

private theorem check_xHuge : Verification.check xHuge [] = true := by
  rw [Verification.check_iff]
  exact ⟨2 ^ 64, [], 1, [], bitDecode_bitEncode _, rfl, by decide, by decide, rfl⟩

example : flowShopSchedulingDec xHuge = true :=
  (Verification.dec_iff_check xHuge).mpr ⟨[], by simp, check_xHuge⟩

end MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling
