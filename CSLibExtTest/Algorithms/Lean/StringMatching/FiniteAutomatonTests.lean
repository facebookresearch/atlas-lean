/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.StringMatching.FiniteAutomaton
public meta import Cslib.Algorithms.Lean.TimeM

public section

set_option autoImplicit false

open Cslib.Algorithms.Lean.StringMatching

private meta def verify {A : Nat} (name : String) (pattern text : List (Fin A))
    (expectedTable expectedStates expected : List Nat) (pre scan total : Nat) : IO Unit := do
  let construction := computeTransition pattern
  let cells := construction.ret.toList.map Fin.val
  let automaton := patternAutomaton pattern
  let states := (text.scanl automaton.tr automaton.start).tail.map Fin.val
  let actual := finiteAutomatonMatches pattern text
  unless cells = expectedTable do throw (IO.userError s!"{name}: table mismatch {cells}")
  unless cells.length = (pattern.length + 1) * A do
    throw (IO.userError s!"{name}: dimensions mismatch")
  unless states = expectedStates do throw (IO.userError s!"{name}: states mismatch {states}")
  unless actual.ret = expected do throw (IO.userError s!"{name}: output mismatch {actual.ret}")
  unless construction.time = pre do throw (IO.userError s!"{name}: preprocessing mismatch")
  unless actual.time - construction.time = scan do throw (IO.userError s!"{name}: scan mismatch")
  unless actual.time = total do throw (IO.userError s!"{name}: total mismatch {actual.time}")
  IO.println s!"{name}: cells={cells} states={states} shifts={actual.ret} pre={pre} scan={scan} total={total}"

#eval do
  verify "Figure32.6" ([0, 1, 0, 1, 0, 2, 0] : List (Fin 3)) [0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0]
    [1, 0, 0, 1, 2, 0, 3, 0, 0, 1, 4, 0, 5, 0, 0, 1, 4, 6, 7, 0, 0, 1, 2, 0] [1, 2, 3, 4, 5, 4, 5, 6, 7, 2, 3] [2] 361 23 384
  verify "overlapping accepting row" ([0, 0] : List (Fin 2)) [0, 0, 0, 0]
    [1, 0, 2, 0, 2, 0] [1, 2, 2, 2] [0, 1, 2] 34 11 45
  verify "empty pattern" ([] : List (Fin 2)) [1, 0, 1]
    [0, 0] [0, 0, 0] [0, 1, 2, 3] 4 10 14
  verify "empty alphabet and strings" ([] : List (Fin 0)) []
    [] [] [0] 0 1 1
  verify "pattern longer than text" ([0, 1, 0] : List (Fin 2)) [0]
    [1, 0, 1, 2, 3, 0, 1, 2] [1] [] 54 2 56
  verify "unused alphabet symbol" ([0, 1] : List (Fin 3)) [0, 2, 1, 0, 1]
    [1, 0, 0, 1, 2, 0, 1, 0, 0] [1, 0, 0, 1, 2] [3] 55 11 66
  verify "Exercise32.3-1" ([0, 0, 1, 0, 1] : List (Fin 2)) [0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1]
    [1, 0, 2, 0, 2, 3, 4, 0, 2, 5, 1, 0] [1, 2, 2, 3, 4, 5, 1, 2, 3, 4, 2, 3, 4, 5, 1, 2, 3] [1, 9] 120 36 156
  verify "singleton match" ([0] : List (Fin 1)) [0]
    [1, 1] [1] [0] 6 3 9
  verify "singleton no match" ([1] : List (Fin 2)) [0, 0]
    [0, 1, 0, 1] [0, 0] [] 16 4 20
  verify "nonempty pattern empty text" ([0] : List (Fin 2)) []
    [1, 0, 1, 0] [] [] 16 0 16
  verify "empty strings nonempty alphabet" ([] : List (Fin 2)) []
    [0, 0] [] [0] 4 1 5
  verify "equal lengths" ([0, 1] : List (Fin 2)) [0, 1]
    [1, 0, 1, 2, 1, 0] [1, 2] [0] 33 5 38
  verify "alternating overlap" ([0, 1, 0] : List (Fin 2)) [0, 1, 0, 1, 0]
    [1, 0, 1, 2, 3, 0, 1, 2] [1, 2, 3, 2, 3] [0, 2] 54 12 66
  verify "prefix fallback" ([0, 0, 1] : List (Fin 2)) [0, 0, 0, 0, 1]
    [1, 0, 2, 0, 2, 3, 1, 0] [1, 2, 2, 2, 3] [2] 57 11 68
  verify "unary overlaps" ([0, 0, 0] : List (Fin 1)) [0, 0, 0, 0, 0]
    [1, 2, 3, 3] [1, 2, 3, 3, 3] [0, 1, 2] 17 13 30
  verify "separated matches and failure" ([0, 1] : List (Fin 2)) [1, 0, 0, 1, 1, 0]
    [1, 0, 1, 2, 1, 0] [0, 1, 1, 2, 0, 1] [2] 33 13 46
  verify "overlength partial prefix" ([1, 0, 1, 0] : List (Fin 2)) [1, 0]
    [0, 1, 2, 1, 0, 3, 4, 1, 0, 3] [1, 2] [] 83 4 87

end
