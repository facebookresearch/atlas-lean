/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Parallel.PRAM
import Mathlib.Tactic.NormNum

@[expose] public section

namespace CSLibExtTest.Parallel.PRAM

open Cslib.Parallel.PRAM

/-! ## Pointer jumping below and at the bound -/

/-- Below the bound: on the successor pointer memory
`ptr i = i + 1` with `2` processors, one pointer-jumping step
sends cell `0` to `ptr (ptr 0) = 2`. -/
example : stepCRCW (fun i => i + 1)
    (pointerJumpStep (fun i => i + 1) 2) 0 = 2 := by
  rw [pointerJump_apply]
  norm_num

/-- The same cell, evaluated from the step semantics alone. -/
example : stepCRCW (fun i => i + 1)
    (pointerJumpStep (fun i => i + 1) 2) 0 = 2 := by decide

/-- At the bound `a = n`: no processor writes cell `2`, so it
keeps `ptr 2 = 3`. -/
example : writers (pointerJumpStep (fun i => i + 1) 2) 2 = ∅ := by decide

example : stepCRCW (fun i => i + 1)
    (pointerJumpStep (fun i => i + 1) 2) 2 = 3 := by decide

example : stepCRCW (fun i => i + 1)
    (pointerJumpStep (fun i => i + 1) 2) 2 = 3 := by
  rw [pointerJump_apply]
  norm_num

/-! ## Read legality of pointer jumping -/

/-- Distinct pointers give distinct reads: the successor round
is EREW-legal. -/
example : EREW (pointerJumpStep (fun i => i + 1) 2) :=
  ⟨by decide, pointerJumpStep_crew _ _⟩

/-- Two nodes pointing at node `0` read cell `0` concurrently:
the round is CREW-legal but not EREW-legal. -/
example : CREW (pointerJumpStep (fun _ => 0) 2) := pointerJumpStep_crew _ _

example : ¬ EREW (pointerJumpStep (fun _ => 0) 2) := fun h =>
  absurd (h.1 (a₁ := 0) (a₂ := 1) rfl) (by decide)

/-! ## Concurrent writes -/

/-- Three processors: processor `i` reads cell `i` and writes
the value read plus `10 * i`; processor `0` writes cell `5`,
processors `1` and `2` both write cell `0`. -/
def conflictProg : PramProg ℕ 3 where
  readAddr i := i
  compute i v := v + 10 * i
  writeAddr i := if (i : ℕ) = 0 then some 5 else some 0

/-- Cell `0` has the two writers `1` and `2`. -/
example : writers conflictProg 0 = {1, 2} := by decide

/-- Under memory `a ↦ a + 1` the writers of cell `0` offer
`12` (processor `1`) and `23` (processor `2`). -/
example : writeVal (fun a => a + 1) conflictProg 1 = 12 ∧
    writeVal (fun a => a + 1) conflictProg 2 = 23 := by decide

/-- The least-index writer wins: cell `0` takes processor `1`'s
`12`, not processor `2`'s `23`. -/
example : stepCRCW (fun a => a + 1) conflictProg 0 = 12 := by decide

/-- A single writer: cell `5` takes processor `0`'s value `1`. -/
example : stepCRCW (fun a => a + 1) conflictProg 5 = 1 := by decide

/-- An unwritten cell keeps its value. -/
example : stepCRCW (fun a => a + 1) conflictProg 7 = 8 := by decide

/-- Two writers on cell `0`: the step is not CREW-legal. -/
example : ¬ CREW conflictProg := fun h => by
  have h12 := h 1 2 rfl
  revert h12
  decide

/-- The two writers of cell `0` disagree: the step is not
Common-legal. -/
example : ¬ CommonLegal (fun a => a + 1) conflictProg := fun h =>
  absurd (h 0 1 (by decide) 2 (by decide)) (by decide)

/-- The same write pattern with every processor writing `7`. -/
def commonProg : PramProg ℕ 3 where
  readAddr i := i
  compute _ _ := 7
  writeAddr i := if (i : ℕ) = 0 then some 5 else some 0

/-- All writers agree, so the step is Common-legal although it is
not CREW-legal. -/
theorem commonProg_commonLegal : CommonLegal (fun a => a + 1) commonProg :=
  fun _ _ _ _ _ => rfl

example : ¬ CREW commonProg := fun h => by
  have h12 := h 1 2 rfl
  revert h12
  decide

/-- On the Common-legal step, cell `0` takes the value of either
writer, here the non-least writer `2`. -/
example : stepCRCW (fun a => a + 1) commonProg 0 =
    writeVal (fun a => a + 1) commonProg 2 :=
  stepCRCW_of_common _ commonProg_commonLegal rfl

end CSLibExtTest.Parallel.PRAM
