/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.MultiTape.TimeSpace
public import CSLibExtTest.Computability.Machines.Turing.MultiTape.BasicTests

@[expose] public section

/-!
# Tests for time and space bounds and the deterministic classes

The language of words starting with `true` is decided by `firstBitTM` (from `BasicTests`) in time
`1` and space `0`, so it lies in `DTIME 1`, in `P` and in `PSPACE`.
-/

set_option autoImplicit false

open Cslib.Turing.MultiTapeTM _root_.Turing

namespace CSLibExtTest.Computability.Machines.Turing.MultiTape

/-- Words whose first bit is `true`. -/
def startsWithTrue : Set (List Bool) := {w | w.head? = some true}

theorem firstBitTM_timeBoundedBy : TimeBoundedBy firstBitTM fun _ ↦ 1 :=
  fun w ↦ MultiTapeTM.runsInTime_of_halted (firstBitTM_runFrom_one w).1

theorem firstBitTM_spaceBoundedBy : SpaceBoundedBy firstBitTM fun _ ↦ 0 :=
  fun w ↦ MultiTapeNTM.runsInSpace_zero_tapes _ w 0

theorem firstBitTM_decides : Decides firstBitTM startsWithTrue := by
  intro w
  refine ⟨1, (firstBitTM_runFrom_one w).1, ?_⟩
  rw [(firstBitTM_runFrom_one w).2]
  by_cases h : w.head? = some true
  · simp [MultiTapeTM.indicator, startsWithTrue, h]
  · simp [MultiTapeTM.indicator, startsWithTrue, h]

theorem startsWithTrue_mem_DTIME : startsWithTrue ∈ DTIME fun _ ↦ 1 :=
  mem_DTIME_iff.mpr ⟨1, 0, 0, Unit, inferInstance, firstBitTM, firstBitTM_decides,
    firstBitTM_timeBoundedBy.mono fun _ ↦ le_rfl, _, firstBitTM_spaceBoundedBy⟩

theorem startsWithTrue_mem_P : startsWithTrue ∈ Classes.P :=
  Set.mem_iUnion.mpr ⟨0, by simpa using startsWithTrue_mem_DTIME⟩

example : startsWithTrue ∈ Classes.PSPACE := Classes.P_subset_PSPACE startsWithTrue_mem_P

example : startsWithTrue ∈ DSPACE fun _ ↦ 0 :=
  mem_DSPACE_iff.mpr ⟨1, 0, 0, Unit, inferInstance, firstBitTM, firstBitTM_decides,
    firstBitTM_spaceBoundedBy.mono fun _ ↦ Nat.zero_le _, _, firstBitTM_timeBoundedBy⟩

/-- The generic space bound from time: zero work tapes give space `0 * (1 + 1)`. -/
example : SpaceBoundedBy firstBitTM fun n ↦ 0 * ((fun _ ↦ 1) n + 1) :=
  firstBitTM_timeBoundedBy.spaceBoundedBy

/-- A constant-time class sits inside every polynomial-time level, by `DTIME_mono`. -/
example (d : ℕ) : DTIME (fun _ ↦ 1) ⊆ DTIME (· ^ d) :=
  DTIME_mono 0 1 fun _ ↦ by simp

end CSLibExtTest.Computability.Machines.Turing.MultiTape
