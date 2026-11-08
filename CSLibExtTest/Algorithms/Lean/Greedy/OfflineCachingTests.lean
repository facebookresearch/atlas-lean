/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Greedy.OfflineCaching
public meta import CSLibExt.Algorithms.Lean.Greedy.OfflineCaching

/-!
# Finite offline caching regression tests

The fixtures check the actual emitted events, request projection, saved final cache,
and miss count. The LRU comparison is a test-only reference, not a formalized LRU
implementation or its correctness theorem.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace CSLibExtTest.Algorithms.Lean.Greedy.OfflineCaching

open Cslib.Algorithms.Lean.OfflineCaching

private meta def verify (label : String) (capacity : Nat) (requests initial : List Nat)
    (expectedEvents : List (CacheEvent Nat)) (expectedCache : List Nat)
    (expectedMisses : Nat) (expectedRequests : List Nat := requests) : IO Unit := do
  let actual := furthestInFuture capacity requests initial
  unless actual.1 = expectedEvents do
    throw <| IO.userError s!"{label}: wrong events {repr actual.1}"
  unless actual.2 = expectedCache do
    throw <| IO.userError s!"{label}: wrong cache {repr actual.2}"
  let emitted := actual.1.map (fun event => match event with
    | .hit request => request | .miss request _ => request)
  unless emitted = expectedRequests do
    throw <| IO.userError s!"{label}: wrong requests {emitted}"
  let misses := actual.1.countP (fun event => match event with
    | .hit _ => false | .miss _ _ => true)
  unless misses = expectedMisses do
    throw <| IO.userError s!"{label}: wrong misses {misses}, expected {expectedMisses}"
  IO.println s!"{label}: events={repr actual.1}, cache={actual.2}, misses={misses}"

private meta def runTests : IO Unit := do
  verify "empty requests" 2 [] [1, 2] [] [1, 2] 0
  verify "zero capacity" 0 [1, 1, 2] []
    [.miss 1 none, .miss 1 none, .miss 2 none] [] 3
  verify "fill and repeat hits" 2 [1, 1, 2, 2] []
    [.miss 1 none, .hit 1, .miss 2 none, .hit 2] [2, 1] 2
  verify "initial full cache" 2 [1, 3, 2] [1, 2]
    [.hit 1, .miss 3 (some 1), .hit 2] [3, 2] 1
  verify "never used victim" 2 [3, 1] [1, 2]
    [.miss 3 (some 2), .hit 1] [3, 1] 1
  verify "first maximal tie" 2 [3] [1, 2] [.miss 3 (some 1)] [3, 2] 1
  verify "finite compensation" 2 [3, 1, 2] [1, 2]
    [.miss 3 (some 2), .hit 1, .miss 2 (some 3)] [2, 1] 2
  verify "capacity one" 1 [1, 2, 1] []
    [.miss 1 none, .miss 2 (some 1), .miss 1 (some 2)] [1] 3
  let requests := [1, 2, 3, 4, 1, 2, 5, 1, 2, 3, 4, 5]
  verify "CLRS versus LRU" 3 requests []
    [.miss 1 none, .miss 2 none, .miss 3 none, .miss 4 (some 3), .hit 1, .hit 2,
      .miss 5 (some 4), .hit 1, .hit 2, .miss 3 (some 2), .miss 4 (some 3), .hit 5]
    [4, 5, 1] 7
  let reference : List Nat × Nat := requests.foldl (fun (cache, misses) request =>
    if request ∈ cache then (request :: cache.erase request, misses)
    else (request :: cache.take 2, misses + 1)) ([], 0)
  unless reference.2 = 10 do
    throw <| IO.userError s!"test-only LRU reference: expected 10 misses, got {reference.2}"
  IO.println s!"test-only capacity-three LRU reference: misses={reference.2}"

#eval runTests

-- Permutations preserve residency, including on hits and both positive-capacity misses.
example : (cacheLTS 2).Tr [1, 2] (.hit 1) [2, 1] := by
  simp only [cacheLTS]
  decide
example : (cacheLTS 3).Tr [1, 2] (.miss 3 none) [2, 3, 1] := by
  simp only [cacheLTS]
  decide
example : (cacheLTS 2).Tr [1, 2] (.miss 3 (some 1)) [2, 3] := by
  simp only [cacheLTS]
  decide
example : (cacheLTS 0).Tr ([] : List Nat) (.miss 1 none) [] := by
  simp only [cacheLTS]
  decide

-- Illegal discard, premature eviction, nonresident victim, and prefetch are excluded.
example : ¬ (cacheLTS 2).Tr [1, 2] (.hit 1) [1] := by
  simp only [cacheLTS]
  decide
example : ¬ (cacheLTS 3).Tr [1, 2] (.miss 3 (some 1)) [3, 2] := by
  simp only [cacheLTS]
  decide
example : ¬ (cacheLTS 2).Tr [1, 2] (.miss 3 (some 9)) [3, 1] := by
  simp only [cacheLTS]
  decide
example : ¬ (cacheLTS 3).Tr [1, 2] (.miss 3 none) [3, 9, 1] := by
  simp only [cacheLTS]
  decide

-- Invalid initial data fails the stated domain; no runtime rejection is promised.
example : ¬ ([1, 1] : List Nat).Nodup := by decide
example : ¬ ([1, 2] : List Nat).length ≤ 1 := by decide
example : ¬ ([1] : List Nat).length ≤ 0 := by decide

end CSLibExtTest.Algorithms.Lean.Greedy.OfflineCaching
