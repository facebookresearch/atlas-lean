/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.Graph.ShortestPath.FasterAPSP
public meta import Mathlib.Algebra.Tropical.BigOperators

/-! All sixteen source and boundary cases execute the actual doubling worker. -/

set_option autoImplicit false

open Cslib.Algorithms.Lean.Matrix

namespace FasterAPSPTests

private meta def verify {n : Nat} (label : String)
    (input expected : Vector (Vector (WithTop Int) n) n)
    (count : Nat × (Nat × Nat)) : IO Unit := do
  let actual := fasterAPSP (input.map (fun row => row.map MinTropical.trop))
  let output := actual.ret.map (fun row => row.map MinTropical.untrop)
  unless decide (output = expected) do
    throw <| IO.userError s!"{label}: wrong cells {repr output}"
  unless actual.time == count do
    throw <| IO.userError s!"{label}: wrong counts {actual.time}"
  IO.println s!"{label}: all {n * n} cells checked; time={actual.time}; output={repr output}"

#eval verify "figure23.1"
  (#v[#v[0, 3, 8, ⊤, -4],
    #v[⊤, 0, ⊤, 1, 7],
    #v[⊤, 4, 0, ⊤, ⊤],
    #v[2, ⊤, -5, 0, ⊤],
    #v[⊤, ⊤, ⊤, 6, 0]] : Vector (Vector (WithTop Int) 5) 5)
  #v[#v[0, 1, -3, 2, -4],
    #v[3, 0, -4, 1, -1],
    #v[7, 4, 0, 5, 3],
    #v[2, -1, -5, 0, -2],
    #v[8, 5, 1, 6, 0]] (125, (250, 250))

#eval verify "figure23.2"
  (#v[#v[0, ⊤, ⊤, ⊤, -1, ⊤],
    #v[1, 0, ⊤, 2, ⊤, ⊤],
    #v[⊤, 2, 0, ⊤, ⊤, -8],
    #v[-4, ⊤, ⊤, 0, 3, ⊤],
    #v[⊤, 7, ⊤, ⊤, 0, ⊤],
    #v[⊤, 5, 10, ⊤, ⊤, 0]] : Vector (Vector (WithTop Int) 6) 6)
  #v[#v[0, 6, ⊤, 8, -1, ⊤],
    #v[-2, 0, ⊤, 2, -3, ⊤],
    #v[-5, -3, 0, -1, -6, -8],
    #v[-4, 2, ⊤, 0, -5, ⊤],
    #v[5, 7, ⊤, 9, 0, ⊤],
    #v[3, 5, 10, 7, 2, 0]] (252, (648, 648))

#eval verify "empty"
  (#v[] : Vector (Vector (WithTop Int) 0) 0)
  #v[] (0, (0, 0))

#eval verify "single-zero"
  (#v[#v[0]] : Vector (Vector (WithTop Int) 1) 1)
  #v[#v[0]] (1, (0, 0))

#eval verify "single-arbitrary-negative"
  (#v[#v[-3]] : Vector (Vector (WithTop Int) 1) 1)
  #v[#v[-3]] (1, (0, 0))

#eval verify "single-infinite"
  (#v[#v[⊤]] : Vector (Vector (WithTop Int) 1) 1)
  #v[#v[⊤]] (1, (0, 0))

#eval verify "two-signed"
  (#v[#v[0, -2],
    #v[⊤, 0]] : Vector (Vector (WithTop Int) 2) 2)
  #v[#v[0, -2],
    #v[⊤, 0]] (4, (0, 0))

#eval verify "threshold-n3"
  (#v[#v[0, 1, ⊤],
    #v[⊤, 0, 1],
    #v[⊤, ⊤, 0]] : Vector (Vector (WithTop Int) 3) 3)
  #v[#v[0, 1, 2],
    #v[⊤, 0, 1],
    #v[⊤, ⊤, 0]] (27, (27, 27))

#eval verify "threshold-n4"
  (#v[#v[0, 1, ⊤, ⊤],
    #v[⊤, 0, 1, ⊤],
    #v[⊤, ⊤, 0, 1],
    #v[⊤, ⊤, ⊤, 0]] : Vector (Vector (WithTop Int) 4) 4)
  #v[#v[0, 1, 2, 3],
    #v[⊤, 0, 1, 2],
    #v[⊤, ⊤, 0, 1],
    #v[⊤, ⊤, ⊤, 0]] (80, (128, 128))

#eval verify "threshold-n5"
  (#v[#v[0, 1, ⊤, ⊤, ⊤],
    #v[⊤, 0, 1, ⊤, ⊤],
    #v[⊤, ⊤, 0, 1, ⊤],
    #v[⊤, ⊤, ⊤, 0, 1],
    #v[⊤, ⊤, ⊤, ⊤, 0]] : Vector (Vector (WithTop Int) 5) 5)
  #v[#v[0, 1, 2, 3, 4],
    #v[⊤, 0, 1, 2, 3],
    #v[⊤, ⊤, 0, 1, 2],
    #v[⊤, ⊤, ⊤, 0, 1],
    #v[⊤, ⊤, ⊤, ⊤, 0]] (125, (250, 250))

#eval verify "threshold-n6"
  (#v[#v[0, 1, ⊤, ⊤, ⊤, ⊤],
    #v[⊤, 0, 1, ⊤, ⊤, ⊤],
    #v[⊤, ⊤, 0, 1, ⊤, ⊤],
    #v[⊤, ⊤, ⊤, 0, 1, ⊤],
    #v[⊤, ⊤, ⊤, ⊤, 0, 1],
    #v[⊤, ⊤, ⊤, ⊤, ⊤, 0]] : Vector (Vector (WithTop Int) 6) 6)
  #v[#v[0, 1, 2, 3, 4, 5],
    #v[⊤, 0, 1, 2, 3, 4],
    #v[⊤, ⊤, 0, 1, 2, 3],
    #v[⊤, ⊤, ⊤, 0, 1, 2],
    #v[⊤, ⊤, ⊤, ⊤, 0, 1],
    #v[⊤, ⊤, ⊤, ⊤, ⊤, 0]] (252, (648, 648))

#eval verify "threshold-n9"
  (#v[#v[0, 1, ⊤, ⊤, ⊤, ⊤, ⊤, ⊤, ⊤],
    #v[⊤, 0, 1, ⊤, ⊤, ⊤, ⊤, ⊤, ⊤],
    #v[⊤, ⊤, 0, 1, ⊤, ⊤, ⊤, ⊤, ⊤],
    #v[⊤, ⊤, ⊤, 0, 1, ⊤, ⊤, ⊤, ⊤],
    #v[⊤, ⊤, ⊤, ⊤, 0, 1, ⊤, ⊤, ⊤],
    #v[⊤, ⊤, ⊤, ⊤, ⊤, 0, 1, ⊤, ⊤],
    #v[⊤, ⊤, ⊤, ⊤, ⊤, ⊤, 0, 1, ⊤],
    #v[⊤, ⊤, ⊤, ⊤, ⊤, ⊤, ⊤, 0, 1],
    #v[⊤, ⊤, ⊤, ⊤, ⊤, ⊤, ⊤, ⊤, 0]] : Vector (Vector (WithTop Int) 9) 9)
  #v[#v[0, 1, 2, 3, 4, 5, 6, 7, 8],
    #v[⊤, 0, 1, 2, 3, 4, 5, 6, 7],
    #v[⊤, ⊤, 0, 1, 2, 3, 4, 5, 6],
    #v[⊤, ⊤, ⊤, 0, 1, 2, 3, 4, 5],
    #v[⊤, ⊤, ⊤, ⊤, 0, 1, 2, 3, 4],
    #v[⊤, ⊤, ⊤, ⊤, ⊤, 0, 1, 2, 3],
    #v[⊤, ⊤, ⊤, ⊤, ⊤, ⊤, 0, 1, 2],
    #v[⊤, ⊤, ⊤, ⊤, ⊤, ⊤, ⊤, 0, 1],
    #v[⊤, ⊤, ⊤, ⊤, ⊤, ⊤, ⊤, ⊤, 0]] (567, (2187, 2187))

#eval verify "unreachable"
  (#v[#v[0, -3, ⊤, ⊤],
    #v[⊤, 0, ⊤, ⊤],
    #v[⊤, ⊤, 0, 2],
    #v[⊤, ⊤, ⊤, 0]] : Vector (Vector (WithTop Int) 4) 4)
  #v[#v[0, -3, ⊤, ⊤],
    #v[⊤, 0, ⊤, ⊤],
    #v[⊤, ⊤, 0, 2],
    #v[⊤, ⊤, ⊤, 0]] (80, (128, 128))

#eval verify "zero-cycle"
  (#v[#v[0, -2, ⊤],
    #v[2, 0, 4],
    #v[⊤, ⊤, 0]] : Vector (Vector (WithTop Int) 3) 3)
  #v[#v[0, -2, 2],
    #v[2, 0, 4],
    #v[⊤, ⊤, 0]] (27, (27, 27))

#eval verify "negative-cycle"
  (#v[#v[0, -2, ⊤],
    #v[1, 0, 4],
    #v[⊤, ⊤, 0]] : Vector (Vector (WithTop Int) 3) 3)
  #v[#v[-1, -2, 2],
    #v[1, -1, 4],
    #v[⊤, ⊤, 0]] (27, (27, 27))

#eval verify "positive-nondiagonal-semantics"
  (#v[#v[2, 9, ⊤],
    #v[⊤, 3, 7],
    #v[⊤, ⊤, 4]] : Vector (Vector (WithTop Int) 3) 3)
  #v[#v[4, 11, 16],
    #v[⊤, 6, 10],
    #v[⊤, ⊤, 8]] (27, (27, 27))

end FasterAPSPTests
