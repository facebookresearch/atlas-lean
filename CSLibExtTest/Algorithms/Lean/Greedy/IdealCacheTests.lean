/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Greedy.IdealCache
meta import CSLibExt.Algorithms.Lean.Greedy.IdealCache
meta import CSLibExt.Algorithms.Lean.Greedy.OfflineCaching

/-! # Regressions for the finite-trace ideal cache -/

set_option autoImplicit false

namespace CSLibExtTest.Algorithms.Lean.Greedy.IdealCache

open Cslib.Algorithms.Lean.IdealCache Cslib.Algorithms.Lean.OfflineCaching

private def cache : Config := ⟨10, 4, by decide, by decide⟩

-- The two unused words do not make a third line; division respects alignment boundaries.
example : cache.lineCapacity = 2 := by decide
example : cache.lineRequests [0, 3, 4, 7, 8] = [0, 0, 1, 1, 2] := by decide

example : cache.cacheMisses [] = 0 := by
  simp [Config.cacheMisses, Config.run, Config.lineRequests, furthestInFuture_nil, misses]

private meta def checkRun (cache : Config) : IO Unit := do
  -- Distinct words in the same line hit after the first access.
  unless cache.cacheMisses [0, 3, 4, 7, 8] == 3 do
    throw (IO.userError "Aligned scan should miss once in each of three lines")
  -- At the fourth request, line 0 was used most recently but is needed later than line 1.
  -- The optimal policy evicts 0, unlike LRU. The last request then misses again.
  let accesses := [0, 4, 1, 8, 5, 3]
  unless (cache.run accesses).1[3]? == some (CacheEvent.miss 2 (some 0)) do
    throw (IO.userError "A full ideal cache should evict the line used furthest in the future")
  unless cache.cacheMisses accesses == 4 do
    throw (IO.userError "The two-line optimal replacement fixture should incur four misses")

#eval checkRun ⟨10, 4, by decide, by decide⟩

end CSLibExtTest.Algorithms.Lean.Greedy.IdealCache
