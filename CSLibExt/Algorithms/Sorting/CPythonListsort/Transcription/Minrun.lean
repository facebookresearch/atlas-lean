/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.Word

/-!
# Adaptive-minrun transcription

Sources: `Objects/listobject.c`, lines 2230-2268 (`merge_init`) and
2745-2754 (`minrun_next`) at CPython commit
`67e6be72be9c0b75a31795ed42f9afb5eb431d47`.
-/

namespace CPythonListsort

/-- The adaptive-minrun fields of CPython's `MergeState`. -/
structure MinrunState where
  listlen : PySSize
  mr_current : PySSize
  mr_e : PySSize
  mr_mask : PySSize
  deriving DecidableEq, Repr

/-- Result of the bounded transcription of `merge_init`'s exponent loop. -/
structure MinrunInitTrace where
  state : MinrunState
  stopped : Bool
  deriving DecidableEq, Repr

/--
The loop
`while (list_size >> mr_e >= MAX_MINRUN) { ++mr_e; }`, with explicit fuel.
-/
def minrunExponentLoop : Nat → PySSize → Nat → Nat × Bool
  | 0, _, exponent => (exponent, false)
  | fuel + 1, listSize, exponent =>
      if (listSize.sshiftRight exponent).slt MAX_MINRUN then
        (exponent, true)
      else
        minrunExponentLoop fuel listSize (exponent + 1)

/-- The adaptive-minrun portion of CPython's `merge_init`, with loop status. -/
def minrunInitTraced (listSize : PySSize) : MinrunInitTrace :=
  let exponentResult := minrunExponentLoop 64 listSize 0
  let exponent : PySSize := BitVec.ofNat 64 exponentResult.1
  { state :=
      { listlen := listSize
        mr_current := 0
        mr_e := exponent
        -- C's unsuffixed literal makes this an `int` expression; the selected
        -- platform fixes `int` at 32 bits and records that bit pattern here.
        mr_mask := ((((1 : BitVec 32) <<< exponentResult.1) - 1).zeroExtend 64) }
    stopped := exponentResult.2 }

/-- The adaptive-minrun fields produced by the transcribed `merge_init` fragment. -/
def minrunInit (listSize : PySSize) : MinrunState :=
  (minrunInitTraced listSize).state

/-- Observable result of one transcribed `minrun_next` call. -/
structure MinrunNextResult where
  state : MinrunState
  result : PySSize
  assertionPassed : Bool
  deriving DecidableEq, Repr

/--
Transcription of `minrun_next`: add, check the signed-overflow assertion,
compute the shifted result, then retain the masked residual.
-/
def minrunNext (state : MinrunState) : MinrunNextResult :=
  let current := state.mr_current + state.listlen
  let result := current.sshiftRight state.mr_e.toNat
  { state := { state with mr_current := current &&& state.mr_mask }
    result := result
    assertionPassed := !current.msb }

/-- Observable result of repeatedly calling the transcribed `minrun_next`. -/
structure MinrunRunResult where
  state : MinrunState
  outputs : List Nat
  assertionsPassed : Bool
  deriving DecidableEq, Repr

/-- Repeated `minrun_next` calls, retaining every emitted target length. -/
def minrunNextN : Nat → MinrunState → MinrunRunResult
  | 0, state => { state := state, outputs := [], assertionsPassed := true }
  | calls + 1, state =>
      let next := minrunNext state
      let tail := minrunNextN calls next.state
      { state := tail.state
        outputs := next.result.toNat :: tail.outputs
        assertionsPassed := next.assertionPassed && tail.assertionsPassed }

end CPythonListsort
