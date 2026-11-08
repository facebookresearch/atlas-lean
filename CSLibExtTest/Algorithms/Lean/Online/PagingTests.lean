/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Online.Paging
public meta import CSLibExt.Algorithms.Lean.Online.Paging

/-!
# LRU paging tests

Executed fixtures: on 300 pseudo-random request sequences over 6 pages, for capacities 1 to 5,
LRU's misses are compared with the optimal (furthest-in-future) manager's: the bound
`lruMisses ≤ k * OPT + k` holds, LRU's own trace serves the requests with `lruMisses` misses, and
the worst observed ratio is printed. On the cyclic sequence over `k + 1` pages LRU misses every
request while the optimum misses about once every `k` requests, so the factor `k` is attained.
Each run throws on a violation. Closed checks instantiate the theorems.
-/

namespace Cslib.Algorithms.Lean.Online.Paging

open Cslib.Algorithms.Lean.OfflineCaching

private meta def optMisses (k : ℕ) (σ : List ℕ) : ℕ := misses (furthestInFuture k σ []).1

#eval do
  let mut s := 5
  let mut worst : ℕ × ℕ := (0, 1)
  for k in [1, 2, 3, 4, 5] do
    for _ in [0:60] do
      let mut σ : List ℕ := []
      for _ in [0:40] do
        s := (s * 1103515245 + 12345) % 2147483648
        σ := σ ++ [s / 11 % 6]
      let l := lruMisses k [] σ
      let o := optMisses k σ
      unless l ≤ k * o + k do throw (IO.userError s!"k = {k}: LRU {l}, OPT {o} on {σ}")
      unless (lruTrace k [] σ).map CacheEvent.request == σ && misses (lruTrace k [] σ) == l do
        throw (IO.userError s!"k = {k}: LRU trace mismatch on {σ}")
      if l * worst.2 > worst.1 * o then worst := (l, o)
  IO.println s!"300 random sequences, k = 1..5: LRU ≤ k * OPT + k; worst LRU/OPT = \
    {worst.1}/{worst.2}"

#eval do
  for k in [2, 3, 4] do
    let σ := (List.range (10 * (k + 1))).map (· % (k + 1))
    let l := lruMisses k [] σ
    let o := optMisses k σ
    unless l == σ.length do throw (IO.userError s!"k = {k}: LRU missed {l} of {σ.length}")
    IO.println s!"cyclic over {k + 1} pages, {σ.length} requests, k = {k}: LRU {l}, OPT {o}"

/-! Closed checks -/

-- the event API of `Greedy/OfflineCaching.lean`
example : misses [CacheEvent.hit 1, .miss 2 none, .miss 3 (some 1)] = 2 ∧
    [CacheEvent.hit 1, .miss 2 none].map CacheEvent.request = [1, 2] := by
  constructor <;> decide

example (σ : List ℕ) :
    misses (lruTrace 3 [] σ) ≤ 3 * misses (furthestInFuture 3 σ []).1 + 3 :=
  lruMisses_le_furthestInFuture (by decide) List.nodup_nil (by decide) σ List.nodup_nil
    (by decide)

example (σ : List ℕ) : (cacheLTS 3).MTr [] (lruTrace 3 [] σ) (lruCache 3 [] σ) :=
  (lruTrace_spec [] σ List.nodup_nil (by decide)).1

#print axioms lruMisses_le
#print axioms lruMisses_le_furthestInFuture
#print axioms lruTrace_spec
#print axioms lruMisses_phase
#print axioms one_le_misses
#print axioms furthestInFuture_misses_le

end Cslib.Algorithms.Lean.Online.Paging
