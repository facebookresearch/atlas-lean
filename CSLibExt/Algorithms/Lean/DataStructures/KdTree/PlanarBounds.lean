/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Cslib/Algorithms/Lean/MergeSort/MergeSort.lean` (CSLib), proofs of `merge_time` and
`mergeSort_time_le` adapted in `merge_comparisons` and `sort_comparisons` respectively.
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Sorrachai Yingchareonthawornhcai
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.KdTree.Planar
import all Cslib.Algorithms.Lean.Sort.Merge

/-!
# Bounds for the planar rank index

At each recursion depth the halves of a split and the two parts of a stable partition
conserve their total lengths. The two initial merge sorts also process only a linear
number of records per level. These facts give a work bound on the actual builder,
not just the solution to a recurrence postulated for it.
-/

public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.KdTree.Planar

private theorem fromOrders_nodes (a n xs ys) :
    (fromOrders a n xs ys).1.storedNodes = if n = 0 then 1 else 2 * n - 1 := by
  induction n using Nat.strong_induction_on generalizing a xs ys with
  | ind n ih =>
    match n with
    | 0 => rw [fromOrders]; rfl
    | 1 => cases xs <;> rw [fromOrders] <;> rfl
    | m + 2 =>
      rw [fromOrders]
      simp only [storedNodes]
      rw [ih _ (by omega), ih _ (by omega)]
      split <;> split <;> split <;> omega

/-- **Exact storage of the planar rank index.** Preprocessing any list of $n$ points stores
$2n-1$ kd-tree constructors if $n>0$, or one if $n=0$. Both dictionaries have $n$ entries.
No general position hypothesis is needed for the storage count. -/
theorem preprocess_storage {α : Type} [LinearOrder α] (pts : List (α × α)) :
    let idx := (preprocess pts).1
    idx.tree.storedNodes = (if pts.length = 0 then 1 else 2 * pts.length - 1) ∧
      idx.byX.size = pts.length ∧ idx.byY.size = pts.length := by
  simp [preprocess, fromOrders_nodes]

private theorem cutRank_work_aux {β : Type*} (keys : Array β) (pass : β → Bool)
    (h start len : Nat) (hlen : len < 2 ^ h) : (cutRank keys pass start len).2 ≤ h + 1 := by
  induction h generalizing start len with
  | zero =>
    have : len = 0 := by simpa using hlen
    subst len
    rw [cutRank]
    simp
  | succ h ih =>
    rw [cutRank]
    split
    · simp
    · rw [pow_succ] at hlen
      dsimp only
      by_cases hpass : (keys[start + len / 2]?).any pass
      · simpa only [ite_eq_left hpass, Nat.add_le_add_iff_right] using
          ih (start + len / 2 + 1) (len - (len / 2 + 1)) (by omega)
      · simpa only [ite_eq_right hpass, Nat.add_le_add_iff_right] using
          ih start (len / 2) (by omega)

/-- **Logarithmic work of a rank cut.** On a slice of length $m$, binary rank search
makes at most $\lceil\log_2(m+1)\rceil$ midpoint probes, plus one terminal call.
This bound on work does not require the keys or the predicate to be ordered. -/
theorem cutRank_work_le {β : Type*} (keys : Array β) (pass : β → Bool) (start len : Nat) :
    (cutRank keys pass start len).2 ≤ Nat.clog 2 (len + 1) + 1 :=
  cutRank_work_aux keys pass _ start len (Nat.lt_of_succ_le (Nat.le_pow_clog (by decide) _))

private theorem partition_length {β : Type*} (p : β → Bool) (xs : List β) :
    (xs.partition p).1.length + (xs.partition p).2.length = xs.length := by
  simp only [List.partition_eq_filter_filter]
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp] <;> omega

private theorem fromOrders_work_aux (h a n xs ys) (hn : n ≤ 2 ^ h) :
    (fromOrders a n xs ys).2 ≤ (if n = 0 then 1 else 2 * n - 1) +
      (n + xs.length + ys.length) * h := by
  induction h generalizing a n xs ys with
  | zero =>
    have : n ≤ 1 := by simpa using hn
    rcases n with _ | _ | n
    · simp [fromOrders]
    · cases xs <;> simp [fromOrders]
    · omega
  | succ h ih =>
    rcases n with _ | _ | m
    · simp [fromOrders]
    · cases xs <;> simp [fromOrders]
    · let n := m + 2
      let k := n / 2
      let X := xs.splitAt k
      let Y := ys.partition (fun p => p a ≤ headCoord a X.2 - 1)
      have hx : X.1.length + X.2.length = xs.length := by simp [X, List.splitAt_eq]; omega
      have hy : Y.1.length + Y.2.length = ys.length := partition_length _ _
      rw [pow_succ] at hn
      have hl := ih (nextAxis a) k Y.1 X.1 (by dsimp [k, n]; omega)
      have hr := ih (nextAxis a) (n - k) Y.2 X.2 (by dsimp [k, n]; omega)
      have hk : k ≠ 0 := by dsimp [k, n]; omega
      have hrk : n - k ≠ 0 := by dsimp [k, n]; omega
      simp only [hk, hrk, ↓reduceIte] at hl hr
      have heq : (fromOrders a n xs ys).2 = 1 + k + ys.length +
          (fromOrders (nextAxis a) k Y.1 X.1).2 + (fromOrders (nextAxis a) (n - k) Y.2 X.2).2 := by
        rw [fromOrders]
      change (fromOrders a n xs ys).2 ≤ _
      rw [heq]
      have hsize : (k + Y.1.length + X.1.length) + (n - k + Y.2.length + X.2.length) =
          n + xs.length + ys.length := by
        have : k ≤ n := Nat.div_le_self ..
        omega
      have hsum := Nat.add_le_add hl hr
      rw [add_add_add_comm, ← Nat.add_mul, hsize] at hsum
      change 1 + k + ys.length + _ + _ ≤ 2 * n - 1 + (n + xs.length + ys.length) * (h + 1)
      rw [Nat.mul_succ (n + xs.length + ys.length) h]
      dsimp only [k, n] at *
      omega

private theorem merge_comparisons {β : Type} (le : β → β → Bool) (xs ys : List β) :
    (xs.mergeM ys (fun p q => (⟨le p q, 1⟩ : TimeM Nat Bool))).time ≤ xs.length + ys.length := by
  fun_induction List.mergeM with grind

private theorem sort_comparisons {β : Type} (le : β → β → Bool) (xs : List β) :
    (xs.mergeSortM (fun p q => (⟨le p q, 1⟩ : TimeM Nat Bool))).time ≤
      TimeM.timeMergeSortRec xs.length := by
  fun_induction List.mergeSortM with
  | case1 | case2 => grind [TimeM.timeMergeSortRec]
  | case3 a b xs _ ih1 ih2 =>
    simp only [TimeM.time_bind]
    grw [merge_comparisons]
    simp only [TimeM.ret_mergeSortM, List.length_mergeSort]
    unfold TimeM.timeMergeSortRec
    grind

private theorem scatter_size (ranks : List (Fin 2 → Int)) (v : Array (Fin 2 → Int)) :
    (ranks.foldl (fun arr p => arr.setIfInBounds ((p 0).toNat / 2) p) v).size = v.size := by
  induction ranks generalizing v with
  | nil => rfl
  | cons p ps ih => simp [ih]

/-- **Preprocessing work for a planar leaf kd-tree.** On any input list of length $n$, the
work of both presorts, rank indexing and all recursive median splits together is at most
$7 n\lceil\log_2 n\rceil + 12n + 2$ (the ceiling log at zero is zero). -/
theorem preprocess_work_le {α : Type} [LinearOrder α] (pts : List (α × α)) :
    let n := pts.length
    (preprocess pts).2 ≤ 7 * (n * Nat.clog 2 n) + 12 * n + 2 := by
  dsimp only
  let n := pts.length
  let sx := pts.mergeSortM (fun p q => (⟨decide (p.1 ≤ q.1), 1⟩ : TimeM Nat Bool))
  let sy := sx.ret.zipIdx.mergeSortM (fun p q => (⟨decide (p.1.2 ≤ q.1.2), 1⟩ : TimeM Nat Bool))
  have hsx : sx.ret.length = n := by simp [sx, n]
  have hsy : sy.ret.length = n := by simp [sy, hsx]
  have hwx : sx.time ≤ TimeM.timeMergeSortRec n := sort_comparisons _ _
  have hwy := sort_comparisons (fun p q : (α × α) × Nat => decide (p.1.2 ≤ q.1.2)) sx.ret.zipIdx
  change sy.time ≤ _ at hwy
  rw [List.length_zipIdx, hsx] at hwy
  have hm := TimeM.timeMergeSortRec_le n
  change TimeM.timeMergeSortRec n ≤ n * Nat.clog 2 n at hm
  dsimp only [preprocess]
  change sx.time + sy.time + 2 * TimeM.timeMergeSortRec sx.ret.length +
      (fromOrders 0 sx.ret.length _ _).2 + 10 * sx.ret.length + 1 ≤ _
  rw [hsx]
  generalize hys : List.map _ sy.ret.zipIdx = ranks
  have hlen : ranks.length = n := by simp [← hys, hsy]
  generalize hxs : List.foldl _ _ ranks = xRanks
  have hxlen : xRanks.toList.length = n := by simp [← hxs, scatter_size]
  have ht := fromOrders_work_aux (Nat.clog 2 n) 0 n xRanks.toList ranks
    (Nat.le_pow_clog (by decide) n)
  rw [hxlen, hlen, show n + n + n = 3 * n by omega, Nat.mul_assoc] at ht
  change _ ≤ 7 * (n * Nat.clog 2 n) + 12 * n + 2
  split at ht <;> omega

end Cslib.Algorithms.Lean.KdTree.Planar
