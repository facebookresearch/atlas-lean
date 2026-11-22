/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Parallel.ListRanking
public meta import CSLibExt.Algorithms.Lean.Parallel.ListRanking

/-!
# List ranking tests

Executed fixtures: on 100 pseudo-random collections of linked lists over up to 40 nodes (a random
order cut into random pieces), the table `listRanks` agrees with the ranks computed by walking
the lists, and one round fewer than `⌈log₂ n⌉` falls short on a single list of `n = 2 ^ j + 2`
nodes. Each run throws on a mismatch. Closed checks instantiate the theorems.
-/

namespace Cslib.Algorithms.Lean.Parallel.ListRanking

/-- The rank by walking the list (at most `n` steps). -/
private meta def walk {n : ℕ} (succ : Fin n → Option (Fin n)) (v : Fin n) : ℕ := Id.run do
  let mut cur := succ v
  let mut r := 0
  for _ in [0:n] do
    match cur with
    | none => break
    | some u => r := r + 1; cur := succ u
  return r

#eval do
  let mut s := 5
  for _ in [0:100] do
    s := (s * 1103515245 + 12345) % 2147483648
    let n := s / 11 % 40 + 1
    -- a random order of the nodes
    let mut order : Array ℕ := Array.range n
    for i in [0:n] do
      s := (s * 1103515245 + 12345) % 2147483648
      let j := i + s / 13 % (n - i)
      order := order.swapIfInBounds i j
    -- cut it into pieces: node order[i] points to order[i+1] unless cut
    let mut next : Array (Option ℕ) := Array.replicate n none
    for i in [0:n - 1] do
      s := (s * 1103515245 + 12345) % 2147483648
      if s / 17 % 5 != 0 then next := next.set! order[i]! (some order[i + 1]!)
    let succ : Fin n → Option (Fin n) := fun v =>
      (next.getD v.val none).bind fun u => if h : u < n then some ⟨u, h⟩ else none
    let ranks := listRanks succ
    unless ranks.size == n do throw (IO.userError s!"size {ranks.size} of {n}")
    for v in (List.finRange n : List (Fin n)) do
      unless ranks.getD (v : Fin n).val 0 == walk succ v do
        throw (IO.userError s!"rank mismatch at node {v} of {n}")
  -- one list 0 → 1 → … → n - 1 with n = 2 ^ j + 2: the head has rank 2 ^ j + 1, so j rounds
  -- (distance at most 2 ^ j) fall short and clog 2 n = j + 1 rounds are needed
  for j in [1, 2, 3, 4] do
    let n := 2 ^ j + 2
    let succ : Fin n → Option (Fin n) := fun v => if h : v.val + 1 < n then some ⟨v.val + 1, h⟩
      else none
    let short := (roundsTab succ j).2.getD 0 0
    unless short == 2 ^ j && walk succ ⟨0, Nat.succ_pos _⟩ == 2 ^ j + 1 do
      throw (IO.userError s!"j = {j}: {short}")
    unless Nat.clog 2 n == j + 1 do throw (IO.userError s!"clog at j = {j}")
  IO.println "100 random list collections: listRanks = walked ranks; on a list of 2^j + 2 nodes \
    j rounds give the head distance 2^j, one short of its rank 2^j + 1; clog 2 n = j + 1"

/-! Closed checks -/

example {n : ℕ} (succ : Fin n → Option (Fin n)) (hs : Terminates succ) (v : Fin n) :
    (listRanks succ).getD v 0 = rank hs v := listRanks_getD hs v

#print axioms listRanks_getD
#print axioms rounds_spec

end Cslib.Algorithms.Lean.Parallel.ListRanking
