/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Greedy.OfflineCaching

/-! # The ideal cache on finite word-access traces -/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.IdealCache

open OfflineCaching

/-- Parameters of a fully associative ideal cache: a budget of `cacheWords` words and aligned
lines of `lineWords` consecutive words. At least one positive-length line fits. Word addresses
are natural numbers, so the main-memory address space has no fixed size bound.

Source: Frigo, Leiserson, Prokop, and Ramachandran, *Cache-Oblivious Algorithms*, FOCS 1999,
§1 and Figure 1. -/
structure Config where
  /-- Cache budget in words. -/
  cacheWords : ℕ
  /-- Number of consecutive words in one cache line. -/
  lineWords : ℕ
  /-- A line contains at least one word. -/
  lineWords_pos : 0 < lineWords
  /-- A whole line fits in the cache. -/
  lineWords_le_cacheWords : lineWords ≤ cacheWords

/-- The index of the aligned line containing word address `a`. -/
def Config.lineOf (C : Config) (a : ℕ) : ℕ := a / C.lineWords

/-- The number of whole lines that fit in the word budget. Any unused remainder of the budget
cannot hold another line. -/
def Config.lineCapacity (C : Config) : ℕ := C.cacheWords / C.lineWords

/-- Translate a sequence of word accesses to line requests, preserving order and repetitions. -/
def Config.lineRequests (C : Config) (accesses : List ℕ) : List ℕ := accesses.map C.lineOf

/-- Start with an empty, fully associative cache and serve the translated line requests by
evicting the resident line whose next access is furthest in the future, when eviction is needed.
The events record requested and evicted line indices, not word addresses. -/
def Config.run (C : Config) (accesses : List ℕ) : List (CacheEvent ℕ) × List ℕ :=
  furthestInFuture C.lineCapacity (C.lineRequests accesses) []

/-- **Ideal-cache miss count.** The number of misses on a finite word-access trace with optimal
replacement, starting empty. It counts line fetches, not RAM work, and does not assume a tall
cache. -/
def Config.cacheMisses (C : Config) (accesses : List ℕ) : ℕ := misses (C.run accesses).1

/-- The ideal-cache run is legal and serves exactly the translated requests. -/
theorem Config.run_legal (C : Config) (accesses : List ℕ) :
    let output := C.run accesses
    (cacheLTS C.lineCapacity).MTr [] output.1 output.2 ∧
      output.1.map CacheEvent.request = C.lineRequests accesses := by
  exact ⟨(furthestInFuture_legal C.lineCapacity (C.lineRequests accesses) [] (by simp) (by simp)).1,
    furthestInFuture_requests C.lineCapacity (C.lineRequests accesses) [] (by simp) (by simp)⟩

/-- The ideal-cache miss count is minimal among legal traces starting empty with the same
line capacity and request sequence. -/
theorem Config.cacheMisses_le (C : Config) (accesses : List ℕ) (events : List (CacheEvent ℕ))
    (finalCache : List ℕ) (hlegal : (cacheLTS C.lineCapacity).MTr [] events finalCache)
    (hrequests : events.map CacheEvent.request = C.lineRequests accesses) :
    C.cacheMisses accesses ≤ misses events :=
  furthestInFuture_misses_le C.lineCapacity (C.lineRequests accesses) [] (by simp) (by simp)
    events finalCache hlegal hrequests

end Cslib.Algorithms.Lean.IdealCache
