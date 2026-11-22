/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Parallel.ListPrefix
public meta import CSLibExt.Algorithms.Lean.Parallel.ListPrefix
public import Mathlib.Algebra.FreeMonoid.Basic
public meta import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Suffix sums tests

Executed fixtures: on 100 pseudo-random forests of linked lists (up to 12 nodes), `listSums` with
values `FreeAddMonoid.of v` (a non-commutative monoid) returns, for every node, the list of nodes
from it to the end of its list in order, as a direct walk computes; with unit values in `ℕ` it
returns the ranks plus one (`listRanks`). Each run throws on a disagreement. Closed checks
instantiate the theorems.
-/

namespace Cslib.Algorithms.Lean.Parallel.ListPrefix

open Cslib.Algorithms.Lean.Parallel.ListRanking

#eval do
  let mut s := 17
  for _ in [0:100] do
    s := (s * 1103515245 + 12345) % 2147483648
    let n := s / 7 % 12 + 1
    -- a random order of the nodes, cut into lists
    let mut keyed : Array (ℕ × ℕ) := #[]
    for v in [0:n] do
      s := (s * 1103515245 + 12345) % 2147483648
      keyed := keyed.push (s, v)
    let order := (keyed.qsort (fun p q => p.1 < q.1)).map fun (p : ℕ × ℕ) => p.2
    let mut nxt : Array (Option ℕ) := Array.replicate n none
    for i in [0:n - 1] do
      s := (s * 1103515245 + 12345) % 2147483648
      if s / 13 % 4 != 0 then nxt := nxt.set! (order[i]!) (some order[i + 1]!)
    let succ : Fin n → Option (Fin n) := fun v =>
      (nxt.getD v.val none).bind fun u => if h : u < n then some ⟨u, h⟩ else none
    let sums := listSums succ fun v => FreeAddMonoid.of v.val
    let ones := listSums succ fun _ => (1 : ℕ)
    let ranks := listRanks succ
    for v in List.finRange n do
      -- the direct walk from `v`
      let mut walk : List ℕ := []
      let mut cur : Option (Fin n) := some v
      for _ in [0:n] do
        match cur with
        | some u => walk := walk ++ [u.val]; cur := succ u
        | none => pure ()
      unless FreeAddMonoid.toList (sums.getD v 0) == walk do
        throw (IO.userError s!"suffix sum of {v} is wrong ({n} nodes)")
      unless ones.getD v 0 == ranks.getD v 0 + 1 do
        throw (IO.userError s!"unit sums at {v} are not ranks plus one")
  IO.println "100 random list forests: suffix sums match the walks; unit sums are ranks plus one"

/-! Closed checks -/

example {n : ℕ} {succ : Fin n → Option (Fin n)} (hs : Terminates succ) (x : Fin n → ℕ)
    (v : Fin n) : (listSums succ x).getD v 0 = suffixSum succ x v :=
  listSums_getD hs v

example {n : ℕ} {succ : Fin n → Option (Fin n)} (hs : Terminates succ) (v : Fin n) :
    suffixSum succ (fun _ => (1 : ℕ)) v = rank hs v + 1 :=
  suffixSum_one hs v

#print axioms listSums_getD
#print axioms suffixSum_eq

end Cslib.Algorithms.Lean.Parallel.ListPrefix
