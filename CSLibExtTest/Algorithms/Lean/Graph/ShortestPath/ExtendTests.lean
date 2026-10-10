/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Extend
public meta import CSLibExt.Algorithms.Lean.Matrix.Multiply
public import Mathlib.Algebra.Tropical.BigOperators
public meta import Mathlib.Algebra.Tropical.BigOperators

/-!
# Shortest-path extension runtime checks

Actual saved-accumulator, operand-order, infinity, signed-walk and empty-input
checks, plus every cell of CLRS fourth edition Figure 23.1. Both selected
scalar operation counts are checked on the same canonical matrix worker.
-/

set_option autoImplicit false

open Cslib.Algorithms.Lean.Matrix

namespace CSLibExtTest.Algorithms.Lean.Graph.ShortestPath.ExtendTests

private meta def verify {n : Nat} (label : String)
    (A B C expected : Vector (Vector (WithTop Int) n) n) (count : Nat) : IO Unit := do
  let actual := matrixAccumulate
    (A.map (fun row => row.map MinTropical.trop))
    (B.map (fun row => row.map MinTropical.trop))
    (C.map (fun row => row.map MinTropical.trop))
  let output := actual.ret.map (fun row => row.map MinTropical.untrop)
  unless decide (output = expected) do
    throw <| IO.userError s!"{label}: wrong min-plus output"
  unless actual.time == (count, count) do
    throw <| IO.userError s!"{label}: wrong scalar counts {actual.time}"
  IO.println s!"{label}: all {n * n} cells checked, scalar counts {actual.time}"

#eval verify "singleton-saved" #v[#v[2]] #v[#v[-3]] #v[#v[-9]] #v[#v[-9]] 1

#eval verify "empty" #v[] #v[] #v[] #v[] 0
#eval verify "singleton-source" #v[#v[2]] #v[#v[-3]] #v[#v[⊤]] #v[#v[-1]] 1
#eval verify "all-infinity"
  #v[#v[⊤, ⊤], #v[⊤, ⊤]] #v[#v[⊤, ⊤], #v[⊤, ⊤]]
  #v[#v[⊤, ⊤], #v[⊤, ⊤]] #v[#v[⊤, ⊤], #v[⊤, ⊤]] 8
#eval verify "asymmetric-operand-order"
  #v[#v[0, 7], #v[2, 0]] #v[#v[5, 1], #v[9, 4]]
  #v[#v[⊤, ⊤], #v[⊤, ⊤]] #v[#v[5, 1], #v[7, 3]] 8
#eval verify "same-input-matrix"
  #v[#v[0, 1], #v[4, 0]] #v[#v[0, 1], #v[4, 0]]
  #v[#v[⊤, ⊤], #v[⊤, ⊤]] #v[#v[0, 1], #v[4, 0]] 8
#eval verify "negative-cycle-bounded-step"
  #v[#v[0, -2], #v[1, 0]] #v[#v[0, -2], #v[1, 0]]
  #v[#v[⊤, ⊤], #v[⊤, ⊤]] #v[#v[-1, -2], #v[1, -1]] 8

private meta def sourceWeights : Vector (Vector (WithTop Int) 5) 5 :=
  #v[#v[0, 3, 8, ⊤, -4], #v[⊤, 0, ⊤, 1, 7], #v[⊤, 4, 0, ⊤, ⊤],
    #v[2, ⊤, -5, 0, ⊤], #v[⊤, ⊤, ⊤, 6, 0]]

private meta def sourceTwoEdges : Vector (Vector (WithTop Int) 5) 5 :=
  #v[#v[0, 3, 8, 2, -4], #v[3, 0, -4, 1, 7], #v[⊤, 4, 0, 5, 11],
    #v[2, -1, -5, 0, -2], #v[8, ⊤, 1, 6, 0]]

#eval verify "Figure23.1-L1-to-L2" sourceWeights sourceWeights
  (Vector.replicate 5 (Vector.replicate 5 ⊤)) sourceTwoEdges 125

private meta def sourceThreeEdges : Vector (Vector (WithTop Int) 5) 5 :=
  #v[#v[0, 3, -3, 2, -4], #v[3, 0, -4, 1, -1], #v[7, 4, 0, 5, 11],
    #v[2, -1, -5, 0, -2], #v[8, 5, 1, 6, 0]]

private meta def sourceFourEdges : Vector (Vector (WithTop Int) 5) 5 :=
  #v[#v[0, 1, -3, 2, -4], #v[3, 0, -4, 1, -1], #v[7, 4, 0, 5, 3],
    #v[2, -1, -5, 0, -2], #v[8, 5, 1, 6, 0]]

#eval verify "Figure23.1-L2-to-L3" sourceTwoEdges sourceWeights
  (Vector.replicate 5 (Vector.replicate 5 ⊤)) sourceThreeEdges 125
#eval verify "Figure23.1-L3-to-L4" sourceThreeEdges sourceWeights
  (Vector.replicate 5 (Vector.replicate 5 ⊤)) sourceFourEdges 125
#eval verify "Figure23.1-stability" sourceFourEdges sourceWeights
  (Vector.replicate 5 (Vector.replicate 5 ⊤)) sourceFourEdges 125

end CSLibExtTest.Algorithms.Lean.Graph.ShortestPath.ExtendTests
