/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Sqrt

/-!
# Binary Hamiltonian-cycle verification

CLRS4 printed1056-1058: strict Hamiltonian cycles, ordered certificate verification,
and verified binary languages. This implementation chooses a header-free square
row-major Bool array for graph input and certificate words of width Nat.clog 2 m
with least-significant-first digits; CLRS does not specify this binary codec.
Selected same-execution events count graph/word reads and actual validation/seen writes.
Sqrt/clog arithmetic, loop headers and physical RAM/word/bit/space phases are excluded.
-/

namespace Cslib.Algorithms.Lean.Graph

open Cslib.Algorithms.Lean

@[no_expose] def countedBits (bits : Array Bool) (start : Nat := bits.size) (stop : Nat := 0) :
    Cslib.Algorithms.Lean.TimeM Nat Nat :=
  bits.foldrM (fun bit value => do
    Cslib.Algorithms.Lean.TimeM.tick 1
    pure ((if bit then 1 else 0) + 2 * value)) 0 start stop

private def graphRead (x : Array Bool) (index : Nat) : TimeM Nat Bool := do
  TimeM.tick 1
  pure (x[index]?.getD false)

private def validateGraph (x : Array Bool) (m : Nat) : TimeM Nat Bool := do
  TimeM.tick 1
  if m * m != x.size then return false
  let indices := Array.ofFn fun i : Fin m => i
  let badDiagonal ← indices.findSomeM? (fun i => do
    let bit ← graphRead x (i.val * m + i.val)
    TimeM.tick 1
    pure (if bit then some true else none))
  if badDiagonal.isSome then return false
  let badSymmetry ← indices.findSomeM? (fun i =>
    indices.findSomeM? (fun j => do
      if i.val < j.val then
        let a ← graphRead x (i.val * m + j.val)
        let b ← graphRead x (j.val * m + i.val)
        TimeM.tick 1
        pure (if a != b then some true else none)
      else pure none))
  pure (!badSymmetry.isSome)

/-- **Hamiltonian-cycle verifier.** Given bit strings $x$ and $y$, let
$m = \lfloor \sqrt{|x|} \rfloor$ and let $w$ be the least natural number with $m \le 2^w$. The
verifier reads $x$ as the adjacency matrix of a graph on the vertices $0, \dots, m - 1$, stored
row by row, and $y$ as $m$ words of $w$ bits, the $i$-th word giving a number $v_i$ in binary,
least significant bit first. It accepts exactly when $|x| = m^2$, every diagonal entry of the
matrix is false, the matrix is symmetric, $m \ge 3$, $|y| = mw$, the numbers
$v_0, \dots, v_{m-1}$ are distinct and less than $m$, and $v_i$ is adjacent to
$v_{(i+1) \bmod m}$ for every $i < m$. Along with the answer it returns a step count of the
operations it performs: bit reads from $x$ and $y$, checks and updates. -/
public def verifyHamiltonianCycle (x y : Array Bool) : TimeM Nat Bool := do
  let m := Nat.sqrt x.size
  let valid ← validateGraph x m
  if !valid then return false
  TimeM.tick 1
  if m < 3 then return false
  let w := Nat.clog 2 m
  TimeM.tick 1
  if y.size != m * w then return false
  let mut seen : Vector Bool m := Vector.replicate m false
  let mut first : Option (Fin m) := none
  let mut previous : Option (Fin m) := none
  for i in Array.ofFn (fun i : Fin m => i) do
    let value ← countedBits y ((i.val + 1) * w) (i.val * w)
    TimeM.tick 1
    if h : value < m then
      let vertex : Fin m := ⟨value, h⟩
      TimeM.tick 1
      if seen[vertex] then return false
      TimeM.tick 1
      seen := seen.set value true h
      if let some p := previous then
        let present ← graphRead x (p.val * m + value)
        TimeM.tick 1
        if !present then return false
      else
        first := some vertex
      previous := some vertex
    else
      return false
  match first, previous with
  | some a, some b =>
    let present ← graphRead x (b.val * m + a.val)
    TimeM.tick 1
    pure present
  | _, _ => pure false

end Cslib.Algorithms.Lean.Graph
