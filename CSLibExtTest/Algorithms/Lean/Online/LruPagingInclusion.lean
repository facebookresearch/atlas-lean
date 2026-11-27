/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Online.FifoPaging
import CSLibExt.Algorithms.Lean.Online.LruPagingInclusion

/-!
# LRU paging inclusion fixtures

Repeated requests exercise recency and hit preservation. A zero-capacity cache never holds a
page and misses every request. The textbook FIFO trace exhibits Belady's anomaly instead.
-/

namespace Cslib.Algorithms.Lean.Online.Paging

open Cslib.Algorithms.Lean.Online.FifoPaging

private def repeatedRequests : List ℕ := [1, 2, 1, 3, 1, 2]

example : lruCache 2 [] repeatedRequests = [2, 1] ∧ lruMisses 2 [] repeatedRequests = 4 := by
  decide

example : lruCache 3 [] repeatedRequests = [2, 1, 3] :=
  ((lru_inclusion repeatedRequests).1 3).trans (by decide)

example (requests : List ℕ) {p : ℕ} (hp : p ∈ lruCache 2 [] requests) :
    p ∈ lruCache 3 [] requests :=
  ((lru_inclusion requests).2 (by decide : 2 ≤ 3)).1.subset hp

example : lruCache 0 [] repeatedRequests = [] ∧
    lruMisses 0 [] repeatedRequests = repeatedRequests.length := by
  decide

example : lruMisses 2 [] repeatedRequests ≤ lruMisses 0 [] repeatedRequests :=
  ((lru_inclusion repeatedRequests).2 (by decide : 0 ≤ 2)).2

example :
    let requests : List ℕ := [1, 2, 3, 4, 1, 2, 5, 1, 2, 3, 4, 5]
    (fifoPager ℕ 3).misses (fifoPager ℕ 3).init requests = 9 ∧
      (fifoPager ℕ 4).misses (fifoPager ℕ 4).init requests = 10 := by
  simp only [fifoPager_misses]
  exact fifo_belady_anomaly

end Cslib.Algorithms.Lean.Online.Paging
