/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.Word

/-!
# Transcription of CPython `powerloop`

Source: `Objects/listobject.c`, lines 2652-2691 at CPython commit
`67e6be72be9c0b75a31795ed42f9afb5eb431d47`.

The recursive fuel makes the C loop total without `partial`. Sixty-four
iterations are exposed as an adequacy obligation in the equivalence layer.
-/

namespace CPythonListsort

/-- Observable state of the transcribed `powerloop` loop. -/
structure PowerloopState where
  result : Nat
  a : PySSize
  b : PySSize
  stopped : Bool
  deriving DecidableEq, Repr

/-- One iteration of CPython's `for (;;)` body, including its pre-test increment. -/
def powerloopStep (n : PySSize) (state : PowerloopState) : PowerloopState :=
  if state.stopped then
    state
  else
    let state := { state with result := state.result + 1 }
    let state :=
      if !state.a.slt n then
        { state with a := state.a - n, b := state.b - n }
      else if !state.b.slt n then
        { state with stopped := true }
      else
        state
    if state.stopped then
      state
    else
      { state with a := state.a <<< 1, b := state.b <<< 1 }

/-- Iterate the transcribed loop for the supplied bound. -/
def powerloopLoop : Nat → PySSize → PowerloopState → PowerloopState
  | 0, _, state => state
  | fuel + 1, n, state =>
      if state.stopped then state else powerloopLoop fuel n (powerloopStep n state)

/-- Full trace of CPython's `powerloop`, including whether its finite bound stopped. -/
def powerloopTraced (s1 n1 n2 n : PySSize) : PowerloopState :=
  let a := 2 * s1 + n1
  let b := a + n1 + n2
  powerloopLoop 64 n { result := 0, a := a, b := b, stopped := false }

/-- The integer result returned by the transcribed `powerloop`. -/
def powerloop (s1 n1 n2 n : PySSize) : Nat :=
  (powerloopTraced s1 n1 n2 n).result

end CPythonListsort
