/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Online.FifoPaging
public meta import CSLibExt.Algorithms.Lean.Online.FifoPaging

/-!
# FIFO paging tests

Executed fixtures: on 300 pseudo-random request sequences (up to 6 pages, 40 requests, capacity
`k = 1, …, 4`) FIFO's misses satisfy `FIFO ≤ k * OPT + k` against the optimal furthest-in-future
manager, `fifoPager` counts the same misses, its cache stays legal, and `policyMisses (lruStep k)`
equals `lruMisses k`; the worst observed ratio is printed. Belady's anomaly: on
`1 2 3 4 1 2 5 1 2 3 4 5` FIFO misses 9 times with 3 slots and 10 times with 4. Each run throws
on a violation. Closed checks instantiate the theorems, including the tightness of the ratio at
`k = 3`.
-/

namespace Cslib.Algorithms.Lean.Online.FifoPaging

open Cslib.Algorithms.Lean.OfflineCaching Cslib.Algorithms.Lean.Online.Paging

#eval do
  let mut s := 13
  let mut worst : ℕ × ℕ := (0, 1)
  for _ in [0:300] do
    s := (s * 1103515245 + 12345) % 2147483648
    let k := s / 7 % 4 + 1
    s := (s * 1103515245 + 12345) % 2147483648
    let pages := s / 7 % 6 + 1
    let mut σ : List ℕ := []
    for _ in [0:40] do
      s := (s * 1103515245 + 12345) % 2147483648
      σ := σ ++ [s / 11 % pages]
    let f := policyMisses (fifoStep k) [] σ
    unless (fifoPager ℕ k).misses (fifoPager ℕ k).init σ == f do throw (IO.userError "pager")
    let opt := misses (furthestInFuture k σ []).1
    unless f ≤ k * opt + k do throw (IO.userError s!"bound fails: k = {k}, {σ}")
    let fin := σ.foldl (fifoStep k) []
    unless fin.Nodup && fin.length ≤ k do throw (IO.userError s!"illegal cache {fin}")
    unless policyMisses (lruStep k) [] σ == lruMisses k [] σ do throw (IO.userError "LRU")
    if f * worst.2 > worst.1 * (opt + 1) then worst := (f, opt + 1)
  -- Belady's anomaly
  let b : List ℕ := [1, 2, 3, 4, 1, 2, 5, 1, 2, 3, 4, 5]
  let m3 := policyMisses (fifoStep 3) [] b
  let m4 := policyMisses (fifoStep 4) [] b
  unless m3 == 9 && m4 == 10 do throw (IO.userError s!"Belady: {m3}, {m4}")
  IO.println s!"300 random sequences: FIFO ≤ k OPT + k, legal caches, LRU instance agrees; worst \
    FIFO/(OPT + 1) = {worst.1}/{worst.2}; Belady: 9 misses with 3 slots, 10 with 4"

/-! Closed checks -/

example (σ : List ℕ) :
    (fifoPager ℕ 3).misses (fifoPager ℕ 3).init σ ≤ 3 * misses (furthestInFuture 3 σ []).1 + 3 :=
  fifoMisses_le_furthestInFuture (by decide) _ σ List.nodup_nil (by decide)

-- the ratio is tight: ratio `5 / 2 < 3` fails on 4 pages
example (b : ℕ) : ∃ σ : List (Fin 4), 5 * misses (furthestInFuture 3 σ []).1 + b <
    2 * (fifoPager (Fin 4) 3).misses (fifoPager (Fin 4) 3).init σ :=
  fifo_not_competitive_of_lt (by decide) (by decide) b

#print axioms fifoMisses_le
#print axioms policyMisses_le

end Cslib.Algorithms.Lean.Online.FifoPaging
