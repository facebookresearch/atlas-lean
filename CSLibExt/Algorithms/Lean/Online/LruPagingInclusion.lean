/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Online.Paging
public import Mathlib.Data.List.Dedup

/-!
# The inclusion property of LRU

Starting empty, LRU holds a capacity-sized prefix of the same recency list at every time.
Thus increasing the capacity preserves hits and cannot increase the number of misses.
See Arpaci-Dusseau and Arpaci-Dusseau, *Operating Systems: Three Easy Pieces*, Chapter 22.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Online.Paging

variable {α : Type*} [DecidableEq α]

private theorem take_erase_take (p : α) (c : List α) (k : ℕ) :
    ((c.take (k + 1)).erase p).take k = (c.erase p).take k := by
  induction c generalizing k with
  | nil => simp
  | cons q c ih =>
    cases k with
    | zero => simp
    | succ k =>
      by_cases h : q = p
      · subst q
        simp [List.take_take]
      · simp [h, ih]

-- An LRU step only needs the capacity prefix of the recency list.
private theorem lruStep_take (k : ℕ) (c : List α) (p : α) :
    lruStep k (c.take k) p = lruStep k c p := by
  cases k with
  | zero => rfl
  | succ k => simp only [lruStep, List.take_succ_cons, take_erase_take]

-- Keeping the last occurrence and reversing lists the distinct pages in recency order.
private theorem recency_append_singleton (requests : List α) (p : α) :
    (requests ++ [p]).dedup.reverse = p :: requests.dedup.reverse.erase p := by
  induction requests with
  | nil => simp
  | cons q requests ih =>
    by_cases hq : q ∈ requests
    · have hq' : q ∈ requests ++ [p] := List.mem_append_left _ hq
      simpa only [List.cons_append, List.dedup_cons_of_mem hq, List.dedup_cons_of_mem hq'] using ih
    · by_cases hqp : q = p
      · subst q
        have hp : p ∈ requests ++ [p] := by simp
        have hp' : p ∉ requests.dedup.reverse := by simpa using hq
        rw [List.cons_append, List.dedup_cons_of_mem hp, ih,
          List.dedup_cons_of_notMem hq, List.reverse_cons, List.erase_append_right _ hp',
          List.erase_cons_head, List.append_nil, List.erase_of_not_mem hp']
      · have hq' : q ∉ requests ++ [p] := by simp [hq, hqp]
        rw [List.cons_append, List.dedup_cons_of_notMem hq', List.dedup_cons_of_notMem hq,
          List.reverse_cons, List.reverse_cons, ih, List.erase_append]
        split <;> simp_all [List.erase_of_not_mem]

private theorem lruCache_eq_take (k : ℕ) (requests : List α) :
    lruCache k [] requests = requests.dedup.reverse.take k := by
  induction requests using List.reverseRecOn with
  | nil => simp [lruCache]
  | append_singleton requests p ih =>
    have hstep : lruCache k [] (requests ++ [p]) = lruStep k (lruCache k [] requests) p := by
      simp [lruCache, List.foldl_append]
    rw [hstep, ih, recency_append_singleton, lruStep_take, lruStep]

private theorem lruCache_prefix (requests : List α) {k ℓ : ℕ} (h : k ≤ ℓ) :
    lruCache k [] requests <+: lruCache ℓ [] requests := by
  rw [lruCache_eq_take, lruCache_eq_take]
  exact List.take_prefix_take_left h

private theorem lruMisses_anti (requests : List α) {k ℓ : ℕ} (h : k ≤ ℓ) :
    lruMisses ℓ [] requests ≤ lruMisses k [] requests := by
  induction requests using List.reverseRecOn with
  | nil => simp [lruMisses]
  | append_singleton requests p ih =>
    have hit_preserved (hp : p ∈ lruCache k [] requests) : p ∈ lruCache ℓ [] requests :=
      (lruCache_prefix requests h).subset hp
    have cost_le : (if p ∈ lruCache ℓ [] requests then 0 else 1 : ℕ) ≤
        (if p ∈ lruCache k [] requests then 0 else 1) := by
      by_cases hp : p ∈ lruCache k [] requests
      · simp [hp, hit_preserved hp]
      · by_cases hp' : p ∈ lruCache ℓ [] requests <;> simp [hp, hp']
    simp only [lruMisses_append, lruMisses, Nat.add_zero]
    exact Nat.add_le_add ih cost_le

/-- **The inclusion property of LRU.** After serving any finite request prefix from an empty
cache, LRU at capacity `k` holds the first `k` distinct pages in most-recent-first order.
`requests.dedup` retains each page's last occurrence, so reversing it gives this order.
For `k ≤ ℓ` the smaller cache is a prefix of the larger one, hence every hit at capacity `k`
is also a hit at capacity `ℓ`. The larger cache incurs no more misses on `requests`.
This includes capacity zero. -/
theorem lru_inclusion (requests : List α) :
    (∀ k, lruCache k [] requests = requests.dedup.reverse.take k) ∧
      ∀ {k ℓ : ℕ}, k ≤ ℓ → (lruCache k [] requests <+: lruCache ℓ [] requests) ∧
        lruMisses ℓ [] requests ≤ lruMisses k [] requests :=
  ⟨fun k => lruCache_eq_take k requests, fun h =>
    ⟨lruCache_prefix requests h, lruMisses_anti requests h⟩⟩

end Cslib.Algorithms.Lean.Online.Paging
