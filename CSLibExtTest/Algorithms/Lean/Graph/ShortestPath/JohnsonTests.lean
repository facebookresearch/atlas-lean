/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Johnson.Basic
public meta import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Dijkstra
public meta import CSLibExt.Algorithms.Lean.Graph.ShortestPath.BellmanFord.Correctness

set_option autoImplicit false

open Cslib.Algorithms.Lean

private meta def successCost (n m : Nat) : Nat :=
  n^3 + n*m + (n+1)*(m+n) + 2*n^2 + 4*m + 5*n + 1

private meta def verify {n : Nat} (name : String) (edges : List (BellmanFord.Edge n))
    (expected : List (List (WithTop Int))) : IO Unit := do
  let run := Johnson.johnson edges
  let some distances := run.ret | throw (IO.userError s!"{name}: unexpected negative cycle")
  let actual := (List.finRange n).map fun source =>
    (List.finRange n).map fun target => distances source target
  unless actual == expected do
    throw (IO.userError s!"{name}: wrong matrix {repr actual}")
  unless run.time == successCost n edges.length do
    throw (IO.userError s!"{name}: wrong selected cost {run.time}")
  IO.println s!"{name}: n={n}, m={edges.length}, selectedTime={run.time}, matrix={repr actual}"

private meta def verifyNegative {n : Nat} (name : String)
    (edges : List (BellmanFord.Edge n)) : IO Unit := do
  let run := Johnson.johnson edges
  match run.ret with
  | some _ => throw (IO.userError s!"{name}: missed negative cycle")
  | none => pure ()
  unless edges.length + n + (n+1)*(edges.length+n) ≤ run.time &&
      run.time ≤ successCost n edges.length + 3*(n+1) do
    throw (IO.userError s!"{name}: wrong failure selected cost {run.time}")
  IO.println s!"{name}: n={n}, m={edges.length}, selectedTime={run.time}, negative cycle"

#eval do
  verify (n := 5) "CLRS Figure23.6"
    [⟨0, 1, 3⟩, ⟨0, 2, 8⟩, ⟨0, 4, -4⟩, ⟨1, 3, 1⟩, ⟨1, 4, 7⟩,
      ⟨2, 1, 4⟩, ⟨3, 0, 2⟩, ⟨3, 2, -5⟩, ⟨4, 3, 6⟩]
    [[0, 1, -3, 2, -4], [3, 0, -4, 1, -1], [7, 4, 0, 5, 3],
      [2, -1, -5, 0, -2], [8, 5, 1, 6, 0]]
  verify (n := 0) "empty domain" [] []
  verify (n := 1) "singleton empty" [] [[0]]
  verify (n := 3) "nonnegative alternatives" [⟨0, 2, 10⟩, ⟨0, 1, 3⟩, ⟨1, 2, 4⟩]
    [[0, 3, 7], [⊤, 0, 4], [⊤, ⊤, 0]]
  verify (n := 3) "negative edge disconnected" [⟨0, 1, -7⟩]
    [[0, -7, ⊤], [⊤, 0, ⊤], [⊤, ⊤, 0]]
  verify (n := 2) "parallel unequal" [⟨0, 1, 5⟩, ⟨0, 1, -2⟩] [[0, -2], [⊤, 0]]
  verify (n := 2) "duplicate and zero loop" [⟨0, 0, 0⟩, ⟨0, 1, 4⟩, ⟨0, 1, 4⟩]
    [[0, 4], [⊤, 0]]
  verify (n := 2) "zero weight cycle" [⟨0, 1, -2⟩, ⟨1, 0, 2⟩] [[0, -2], [2, 0]]
  verifyNegative (n := 1) "negative loop" [⟨0, 0, -1⟩]
  verifyNegative (n := 4) "disconnected negative cycle" [⟨1, 2, -3⟩, ⟨2, 1, 1⟩]
  verifyNegative (n := 3) "connected negative cycle"
    [⟨0, 1, 1⟩, ⟨1, 2, -3⟩, ⟨2, 1, 1⟩]
  verify (n := 3) "arbitrary precision cancellation"
    [⟨0, 1, (10 : Int)^30⟩, ⟨1, 2, -(10 : Int)^30 - 7⟩]
    [[0, (10 : Int)^30, -7], [⊤, 0, -(10 : Int)^30 - 7], [⊤, ⊤, 0]]
