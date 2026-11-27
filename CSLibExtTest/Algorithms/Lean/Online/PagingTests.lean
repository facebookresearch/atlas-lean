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
For an optimum with `h ≤ k` pages, the same sequences check the resource-augmented bound
`(k - h + 1) * lruMisses ≤ k * OPT + (k - h + 1) * h`, with both caches empty and with different
initial caches. Each run throws on a violation. Closed checks instantiate the theorems.
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

#eval do
  let mut s := 7
  let mut checked := 0
  for k in [1, 2, 3, 4, 5] do
    for h in (List.range k).map (· + 1) do
      for _ in [0:20] do
        let mut σ : List ℕ := []
        for _ in [0:40] do
          s := (s * 1103515245 + 12345) % 2147483648
          σ := σ ++ [s / 11 % 6]
        let starts : List (List ℕ × List ℕ) := [([], []), (List.range k, [5, 4, 3, 2, 1].take h)]
        for (c, c0) in starts do
          let l := lruMisses k c σ
          let o := misses (furthestInFuture h σ c0).1
          unless (k - h + 1) * l ≤ k * o + (k - h + 1) * h do
            throw (IO.userError s!"k = {k}, h = {h}: LRU {l}, OPT {o} on {σ} from {c}, {c0}")
          checked := checked + 1
  IO.println s!"{checked} runs, 1 ≤ h ≤ k ≤ 5: (k - h + 1) * LRU ≤ k * OPT_h + (k - h + 1) * h"

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

/-- With `h = k`, the resource-augmented bound is the `k`-competitiveness of LRU against the
offline optimum (`lruMisses_le_furthestInFuture`, counted with `lruMisses`). -/
example (k : ℕ) (hk : 1 ≤ k) (c σ : List ℕ) :
    lruMisses k c σ ≤ k * misses (furthestInFuture k σ []).1 + k := by
  simpa using lruMisses_le_furthestInFuture_of_le hk le_rfl c σ List.nodup_nil (Nat.zero_le _)

/-- With `k = 2 h`, LRU misses at most twice as often as the offline optimum with `h` pages,
plus `h`. -/
example (h : ℕ) (hh : 1 ≤ h) (c σ c0 : List ℕ) (hnd : c0.Nodup) (hck : c0.length ≤ h) :
    lruMisses (2 * h) c σ ≤ 2 * misses (furthestInFuture h σ c0).1 + h := by
  have := lruMisses_le_furthestInFuture_of_le (k := 2 * h) hh (by omega) c σ hnd hck
  rw [show 2 * h - h + 1 = h + 1 by omega] at this
  have h2 : 2 * h * misses (furthestInFuture h σ c0).1 ≤
      (h + 1) * (2 * misses (furthestInFuture h σ c0).1) := by
    rw [Nat.mul_comm 2 h, Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.le_succ h)
  refine Nat.le_of_mul_le_mul_left (c := h + 1) ?_ (by omega)
  rw [Nat.mul_add]
  omega

/-- A concrete instance with `k = 2` and `h = 1`: on `1, 2, 1, 2, 3`, LRU with two pages started
empty misses three times, and the bound against the offline optimum with one page started empty
applies. -/
example : lruMisses 2 [] [1, 2, 1, 2, 3] = 3 ∧
    2 * lruMisses 2 [] [1, 2, 1, 2, 3] ≤
      2 * misses (furthestInFuture 1 [1, 2, 1, 2, 3] []).1 + 2 * 1 :=
  ⟨by decide, lruMisses_le_furthestInFuture_of_le (k := 2) (h := 1) le_rfl (by decide) _ _
    List.nodup_nil (by decide)⟩

/-- The additive term is attained when the initial caches differ (`k = 2`, `h = 1`): on the single
request `1`, LRU with two pages started empty misses once, while the offline optimum with one page
started with page `1` cached does not miss, so `2 * 1 = 2 * 0 + 2 * 1`. -/
example : 2 * lruMisses 2 [] [1] = 2 * misses (furthestInFuture 1 [1] [1]).1 + 2 * 1 := by
  rw [(furthestInFuture_cons 1 1 [] [1] (by decide) (by decide)).1 (by decide),
    furthestInFuture_nil]
  decide

#print axioms lruMisses_le_furthestInFuture_of_le
#print axioms lruMisses_le
#print axioms lruMisses_le_furthestInFuture
#print axioms lruTrace_spec
#print axioms lruMisses_phase
#print axioms one_le_misses
#print axioms furthestInFuture_misses_le

end Cslib.Algorithms.Lean.Online.Paging
