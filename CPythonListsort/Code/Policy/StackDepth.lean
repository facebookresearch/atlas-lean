/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Equivalence.PowerloopResults
import Code.Policy.StackPowers
import Code.Transcription.ListSortImpl
import Mathlib

/-!
# Pending-stack depth bound

The powers stored before the caller's unconditional push are distinct members
of the concrete interval `1 .. 60`.  A finite pigeonhole argument therefore
bounds the current stack by `60`; the unbounded modeled push has depth exactly
one larger and remains strictly below CPython's 64-entry pending array.

Nothing in these statements guards, refuses, or clamps the push.  The
`ReadyToPush` premise restricts only the executions for which the capacity
conclusion is proved.
-/

namespace CPythonListsort

universe u v

/-- A strictly increasing list contained in `1 .. POWER_BOUND` has at most
`POWER_BOUND` entries.  This is the finite pigeonhole step behind the pending
stack bound. -/
theorem increasingPowers_length_le_powerBound
    {powers : List Nat}
    (hrange : ∀ power ∈ powers, 1 ≤ power ∧ power ≤ POWER_BOUND)
    (hstrict : powers.Pairwise (· < ·)) :
    powers.length ≤ POWER_BOUND := by
  have hsubset : powers.toFinset ⊆ Finset.Icc 1 POWER_BOUND := by
    intro power hpower
    rw [List.mem_toFinset] at hpower
    exact Finset.mem_Icc.mpr (hrange power hpower)
  have hcard := Finset.card_le_card hsubset
  rw [List.toFinset_card_of_nodup hstrict.nodup] at hcard
  simpa [POWER_BOUND] using hcard

/-- The initialized powers in an `IncreasingPendingPowers` witness occupy at
most all sixty possible values. -/
theorem IncreasingPendingPowers.length_le_powerBound
    {runs : List PendingRun} (h : IncreasingPendingPowers runs) :
    runs.length ≤ POWER_BOUND := by
  rcases h.length_eq with ⟨powers, hlength, hrange, hstrict⟩
  have hrange' : ∀ power ∈ powers, 1 ≤ power ∧ power ≤ POWER_BOUND := by
    simpa [POWER_BOUND] using hrange
  rw [← hlength]
  exact increasingPowers_length_le_powerBound hrange' hstrict

/-- Immediately before the caller pushes the newly discovered run, every
current stack entry has a ranged power, so the current depth is at most 60. -/
theorem ReadyToPush.current_depth_le_sixty
    {state : MergeState κ ν} {scanned : Nat} {newRun : PendingRun}
    (hready : ReadyToPush state scanned newRun) :
    state.pending.size ≤ 60 := by
  have hbound := hready.current_powers.length_le_powerBound
  simpa [POWER_BOUND] using hbound

/-- Exact capacity accounting for the actual unconditional push used by
`list_sort_impl`: the old depth is at most 60, the result is exactly one
larger and at most 61, and 61 is strictly below `MAX_MERGE_PENDING = 64`. -/
theorem readyToPush_stack_depth_bound
    (state : MergeState κ ν) (scanned : Nat) (newRun : PendingRun)
    (hready : ReadyToPush state scanned newRun) :
    state.pending.size ≤ 60 ∧
      (pushPendingRun state newRun).pending.size = state.pending.size + 1 ∧
      (pushPendingRun state newRun).pending.size ≤ 61 ∧
      (pushPendingRun state newRun).pending.size < MAX_MERGE_PENDING := by
  have hcurrent : state.pending.size ≤ 60 :=
    hready.current_depth_le_sixty
  have hexact := pushPendingRun_size state newRun
  refine ⟨hcurrent, hexact, ?_, ?_⟩
  · omega
  · rw [hexact]
    have hcapacity := powerBound_relation.2
    omega

end CPythonListsort
