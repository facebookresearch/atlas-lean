/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Online.PagingLowerBound
public meta import CSLibExt.Algorithms.Lean.Online.PagingLowerBound

/-!
# Paging lower bound tests

Executed fixtures: for `k = 1, …, 5` and `n = 60` requests, the adversary is run against LRU and
against FIFO (evict the oldest page): each misses all `n` requests, while the offline trace
`optTrace` and the optimal furthest-in-future manager miss at most `k + ⌈n / k⌉` times, and
`optTrace` serves exactly the requests. Each run throws on a violation. Closed checks
instantiate the theorems, the lower bound at ratio `5 / 2` for `k = 3`, also for a pager whose
states live in `Type 1`.
-/

namespace Cslib.Algorithms.Lean.Online.Paging

open Cslib.Algorithms.Lean.OfflineCaching

/-- FIFO: on a miss with a full cache, evict the page loaded first (the last of the list). -/
private def fifoPager (k : ℕ) : OnlinePager.{0, 0} (Fin (k + 1)) k where
  State := {c : List (Fin (k + 1)) // c.length ≤ k}
  init := ⟨[], Nat.zero_le _⟩
  cache q := q.1
  step q p := if p ∈ q.1 then q else ⟨(p :: q.1).take k, List.length_take_le _ _⟩
  cache_le q := q.2

private meta def run (k : ℕ) (A : OnlinePager.{0, 0} (Fin (k + 1)) k) (name : String) :
    IO Unit := do
  let n := 60
  let σ := adversary A n A.init
  let online := A.misses A.init σ
  let off := misses (optTrace k [] σ)
  let opt := misses (furthestInFuture k σ []).1
  unless online == n && off ≤ k + (n + k - 1) / k && opt ≤ off &&
      (optTrace k [] σ).map CacheEvent.request == σ do
    throw (IO.userError s!"{name}, k = {k}: online {online}, offline {off}, OPT {opt}")
  IO.println s!"{name}, k = {k}: online {online} of {n}, offline trace {off}, OPT {opt}, \
    bound k + ⌈n/k⌉ = {k + (n + k - 1) / k}"

#eval do
  for k in [1, 2, 3, 4, 5] do
    if 1 ≤ k then
      run k (lruPager (Fin (k + 1)) k) "LRU"
      run k (fifoPager k) "FIFO"

/-! Closed checks -/

-- ratio `5 / 2 < 3`
example (A : OnlinePager (Fin 4) 3) (b : ℕ) :
    ∃ σ : List (Fin 4), 5 * misses (furthestInFuture 3 σ []).1 + b < 2 * A.misses A.init σ :=
  not_competitive_of_lt (by decide) A (by decide) b

-- pagers whose states live in a higher universe are covered too
example (A : OnlinePager.{0, 1} (Fin 4) 3) (b : ℕ) :
    ∃ σ : List (Fin 4), 5 * misses (furthestInFuture 3 σ []).1 + b < 2 * A.misses A.init σ :=
  not_competitive_of_lt (by decide) A (by decide) b

#print axioms not_competitive_of_lt
#print axioms adversary_vs_optimum
#print axioms misses_optTrace_le
#print axioms optTrace_legal
#print axioms lruPager_misses

end Cslib.Algorithms.Lean.Online.Paging
