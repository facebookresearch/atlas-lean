/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Greedy.OfflineCaching

/-!
# Ordinary-import offline caching API regression tests

These generic consumers check the eight frozen declarations without importing private
implementation proofs or unfolding the opaque executable manager.
Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false
namespace CSLibExtTest.Algorithms.Lean.Greedy.OfflineCachingAPI

universe u
open Cslib.Algorithms.Lean.OfflineCaching
variable {α : Type u} [DecidableEq α]

#check (CacheEvent : Type u → Type u)
#check (cacheLTS (α := α) : Nat → Cslib.LTS (List α) (CacheEvent α))
#check (furthestInFuture (α := α) : Nat → List α → List α → List (CacheEvent α) × List α)

example (capacity : Nat) (cache : List α) :
    furthestInFuture capacity [] cache = ([], cache) :=
  furthestInFuture_nil capacity cache

example (capacity : Nat) (request : α) (future cache : List α)
    (hnodup : cache.Nodup) (hcapacity : cache.length ≤ capacity) :
    (request ∈ cache →
      furthestInFuture capacity (request :: future) cache =
        (.hit request :: (furthestInFuture capacity future cache).1,
          (furthestInFuture capacity future cache).2)) ∧
    (capacity = 0 →
      furthestInFuture capacity (request :: future) cache =
        (.miss request none :: (furthestInFuture capacity future []).1,
          (furthestInFuture capacity future []).2)) ∧
    (request ∉ cache → cache.length < capacity →
      furthestInFuture capacity (request :: future) cache =
        (.miss request none :: (furthestInFuture capacity future (request :: cache)).1,
          (furthestInFuture capacity future (request :: cache)).2)) ∧
    (request ∉ cache → 0 < capacity → cache.length = capacity →
      ∀ victim, List.argmax (β := WithTop Nat) (fun block => future.idxOf? block) cache =
          some victim →
        furthestInFuture capacity (request :: future) cache =
          (.miss request (some victim) ::
            (furthestInFuture capacity future (request :: cache.erase victim)).1,
            (furthestInFuture capacity future (request :: cache.erase victim)).2)) :=
  furthestInFuture_cons capacity request future cache hnodup hcapacity

example (capacity : Nat) (requests cache : List α)
    (hnodup : cache.Nodup) (hcapacity : cache.length ≤ capacity) :
    let output := furthestInFuture capacity requests cache
    (cacheLTS capacity).MTr cache output.1 output.2 ∧
      output.1.map (fun event => match event with
        | .hit request => request | .miss request _ => request) = requests ∧
      output.2.Nodup ∧ output.2.length ≤ capacity :=
  furthestInFuture_legal capacity requests cache hnodup hcapacity

example (requests : List α) :
    furthestInFuture 0 requests [] =
      (requests.map (fun request => CacheEvent.miss request none), []) :=
  furthestInFuture_zero_capacity requests

example (capacity : Nat) (requests cache : List α)
    (hnodup : cache.Nodup) (hcapacity : cache.length ≤ capacity)
    (events : List (CacheEvent α)) (finalCache : List α)
    (hlegal : (cacheLTS capacity).MTr cache events finalCache)
    (hrequests : events.map (fun event => match event with
      | .hit request => request | .miss request _ => request) = requests) :
    (furthestInFuture capacity requests cache).1.countP
      (fun event => match event with | .hit _ => false | .miss _ _ => true) ≤
      events.countP (fun event => match event with | .hit _ => false | .miss _ _ => true) :=
  furthestInFuture_min_misses capacity requests cache hnodup hcapacity
    events finalCache hlegal hrequests

-- The competitor deliberately permutes its intermediate cache representations.
example : (furthestInFuture (α := Nat) 2 [3, 1, 2] [1, 2]).1.countP
    (fun event => match event with | .hit _ => false | .miss _ _ => true) ≤ 2 := by
  have htrace : (cacheLTS (α := Nat) 2).MTr [1, 2]
      [.miss 3 (some 1), .miss 1 (some 3), .hit 2] [2, 1] :=
    .stepL (s2 := [2, 3]) (by simp only [cacheLTS]; decide)
      (.stepL (s2 := [1, 2]) (by simp only [cacheLTS]; decide)
        (.stepL (s2 := [2, 1]) (by simp only [cacheLTS]; decide) .refl))
  have hbound := furthestInFuture_min_misses 2 [3, 1, 2] [1, 2] (by decide) (by decide)
    [.miss 3 (some 1), .miss 1 (some 3), .hit 2] [2, 1] htrace rfl
  simp only [List.countP_cons, List.countP_nil, Bool.false_eq_true, ↓reduceIte,
    Nat.zero_add, Nat.reduceAdd] at hbound
  refine Nat.le_trans ?_ hbound
  apply Nat.le_of_eq
  congr 1
  funext event
  cases event <;> rfl

end CSLibExtTest.Algorithms.Lean.Greedy.OfflineCachingAPI
