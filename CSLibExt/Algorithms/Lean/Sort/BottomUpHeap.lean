/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap.BuildHeap

/-!
# Heapsort with bottom-up heap construction

`bottomUpHeapSort` builds a binary min-heap from its input by bottom-up construction
(`buildHeap`) and then extracts the minimum as many times as there are entries, moving the last
entry to the root and sifting it down after each extraction. `TimeM.bottomUpHeapSort` counts
value comparisons and array swaps; erasing the counters gives `bottomUpHeapSort`.

The main theorem bounds the comparisons by `2 * n * (Nat.log 2 n + 1)` for an input of length
`n`: at most `2 * n` for the construction and at most `2 * Nat.log 2 n` for each of the `n`
sift-downs from the root.

Heapsort with bottom-up heap construction is R. W. Floyd's *Algorithm 245: Treesort 3*
(Comm. ACM 7(12), 701, 1964), which sorts in place with a max-heap; here the heap is a min-heap
and the extracted minima are collected in a list.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

set_option autoImplicit false

universe u

variable {α : Type u} [LinearOrder α]

/-- **Heapsort with bottom-up heap construction.** For a list $xs$ of elements of a linearly
ordered type, this heapsort first applies bottom-up heap construction to the array of the entries
of $xs$. Then, as long as the array is nonempty, it outputs the entry at the root (index $0$),
moves the last entry of the array to the root and deletes the last position, and sifts the new
root entry down from index $0$. The output is the list of the entries output, in the order in
which they were output. -/
def bottomUpHeapSort (xs : List α) : List α :=
  drain xs.length (buildHeap xs.toArray)
where
  -- `drain k b` outputs the root of `b` and repairs the heap, at most `k` times.
  drain : Nat → Array α → List α
    | 0, _ => []
    | k + 1, b =>
      if h : 0 < b.size then b[0] :: drain k (siftDown (moveLastToRoot b h) 0) else []

private theorem size_siftDown_moveLastToRoot (b : Array α) (h : 0 < b.size) :
    (siftDown (moveLastToRoot b h) 0).size = b.size - 1 := by
  rw [(siftDown_perm _ _).size_eq]
  simp [moveLastToRoot]

private theorem ordered_siftDown_moveLastToRoot (b : Array α) (hb : HeapOrdered b)
    (h : 0 < b.size) : HeapOrdered (siftDown (moveLastToRoot b h) 0) := by
  by_cases htwo : 1 < b.size
  · exact siftDown_ordered _ 0 (moveLastToRoot_siftDownReady b hb htwo)
  · intro j hj _
    rw [size_siftDown_moveLastToRoot] at hj
    omega

private theorem cons_perm_siftDown_moveLastToRoot (b : Array α) (h : 0 < b.size) :
    (b[0] :: (siftDown (moveLastToRoot b h) 0).toList).Perm b.toList := by
  have hmem : b[0] ∈ (↑b.toList : Multiset α) := by
    simp [Array.mem_toList_iff]
  have hcons : b[0] ::ₘ (↑(moveLastToRoot b h).toList : Multiset α) = ↑b.toList := by
    rw [moveLastToRoot_elements, Multiset.cons_erase hmem]
  exact ((siftDown_perm _ 0).toList.cons _).trans (Multiset.coe_eq_coe.mp hcons)

private theorem drain_correct (k : Nat) (b : Array α) (hb : HeapOrdered b) (hk : b.size = k) :
    List.Pairwise (· ≤ ·) (bottomUpHeapSort.drain k b) ∧
      (bottomUpHeapSort.drain k b).Perm b.toList := by
  induction k generalizing b with
  | zero =>
    have hempty : b = #[] := Array.size_eq_zero_iff.mp hk
    subst hempty
    simp [bottomUpHeapSort.drain]
  | succ k ih =>
    have hpos : 0 < b.size := by omega
    obtain ⟨hsorted, hperm⟩ := ih _ (ordered_siftDown_moveLastToRoot b hb hpos)
      (by rw [size_siftDown_moveLastToRoot]; omega)
    have hall := (hperm.cons b[0]).trans (cons_perm_siftDown_moveLastToRoot b hpos)
    simp only [bottomUpHeapSort.drain, hpos, ↓reduceDIte]
    refine ⟨List.pairwise_cons.2 ⟨fun y hy => ?_, hsorted⟩, hall⟩
    have hyb : y ∈ b.toList := hall.subset (List.mem_cons_of_mem _ hy)
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hyb
    simpa using hb.root_le j (by simpa using hj)

-- Bottom-up heapsort returns a sorted permutation of its input.
theorem bottomUpHeapSort_correct (xs : List α) :
    List.Pairwise (· ≤ ·) (bottomUpHeapSort xs) ∧ (bottomUpHeapSort xs).Perm xs := by
  have hsize : (buildHeap xs.toArray).size = xs.length := by
    rw [(buildHeap_perm _).size_eq, List.size_toArray]
  obtain ⟨hsorted, hperm⟩ :=
    drain_correct xs.length _ (buildHeap_ordered xs.toArray) hsize
  exact ⟨hsorted, hperm.trans (by simpa using (buildHeap_perm xs.toArray).toList)⟩

namespace TimeM

/-- **Heapsort with bottom-up heap construction, with comparison and swap counts.** For a list
$xs$ of elements of a linearly ordered type, timed heapsort runs timed bottom-up heap
construction on the array of the entries of $xs$. Then, as long as the array is nonempty, it
outputs the root entry, moves the last entry to the root and deletes the last position at the
cost of one array swap, and runs timed sift-down from index $0$ on the new array. Costs are
pairs (value comparisons, array swaps), added componentwise; the output is as in heapsort with
bottom-up heap construction. -/
def bottomUpHeapSort (xs : List α) : TimeM (Nat × Nat) (List α) := do
  let b ← buildHeap xs.toArray
  drain xs.length b
where
  -- `drain k b` outputs the root of `b` and repairs the heap, at most `k` times.
  drain : Nat → Array α → TimeM (Nat × Nat) (List α)
    | 0, _ => pure []
    | k + 1, b =>
      if h : 0 < b.size then do
        tick (0, 1)
        let b' ← siftDown (moveLastToRoot b h) 0
        let rest ← drain k b'
        pure (b[0] :: rest)
      else pure []

private theorem ret_drain (k : Nat) (b : Array α) :
    (bottomUpHeapSort.drain k b).ret = Lean.bottomUpHeapSort.drain k b := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
    rw [bottomUpHeapSort.drain, Lean.bottomUpHeapSort.drain]
    split
    · simp [ih, ret_siftDown]
    · rfl

-- Erasing the counters of timed bottom-up heapsort gives bottom-up heapsort.
@[simp]
theorem ret_bottomUpHeapSort (xs : List α) :
    (bottomUpHeapSort xs).ret = Lean.bottomUpHeapSort xs := by
  simp [bottomUpHeapSort, Lean.bottomUpHeapSort, ret_drain]

private theorem drain_comparisons_le (k N : Nat) (b : Array α) (hb : b.size ≤ N) :
    (bottomUpHeapSort.drain k b).time.1 ≤ 2 * k * Nat.log 2 N := by
  induction k generalizing b with
  | zero => simp [bottomUpHeapSort.drain]
  | succ k ih =>
    rw [bottomUpHeapSort.drain]
    split
    · rename_i hpos
      have hs := siftDown_comparisons_le (moveLastToRoot b hpos) 0
      have hsize : (moveLastToRoot b hpos).size ≤ N := by
        simp only [moveLastToRoot, Array.size_pop, Array.size_swap]
        omega
      have hlog : Nat.log2 (moveLastToRoot b hpos).size ≤ Nat.log 2 N := by
        rw [Nat.log2_eq_log_two]
        exact Nat.log_mono_right hsize
      have hrest := ih (siftDown (moveLastToRoot b hpos) 0).ret (by
        rw [ret_siftDown, size_siftDown_moveLastToRoot]
        omega)
      have hone : Nat.log2 1 = 0 := by rw [Nat.log2_eq_log_two, Nat.log_one_right]
      rw [hone, Nat.sub_zero] at hs
      have hsplit : 2 * (k + 1) * Nat.log 2 N = 2 * k * Nat.log 2 N + 2 * Nat.log 2 N := by ring
      simp only [time_bind, time_tick, time_pure, Prod.fst_add, Prod.fst_zero]
      omega
    · simp

/-- **Correctness and comparison bound for heapsort with bottom-up construction.** For every
list $xs$ of length $n$ over a linearly ordered type, the list returned by timed heapsort with
bottom-up heap construction on $xs$ is sorted in nondecreasing order and is a permutation of
$xs$, and the number of value comparisons it counts is at most
$2n(\lfloor \log_2 n \rfloor + 1)$, where $\lfloor \log_2 0 \rfloor$ is read as $0$. -/
theorem bottomUpHeapSort_correct_comparisons_le (xs : List α) :
    List.Pairwise (· ≤ ·) (bottomUpHeapSort xs).ret ∧ (bottomUpHeapSort xs).ret.Perm xs ∧
      (bottomUpHeapSort xs).time.1 ≤ 2 * xs.length * (Nat.log 2 xs.length + 1) := by
  obtain ⟨hsorted, hperm⟩ := bottomUpHeapSort_correct xs
  refine ⟨by simpa using hsorted, by simpa using hperm, ?_⟩
  obtain ⟨-, hbperm, -, hbuild, hsum, -⟩ := buildHeap_linear xs.toArray
  have hsize : (buildHeap xs.toArray).ret.size = xs.length := by
    rw [hbperm.size_eq, List.size_toArray]
  have hdrain := drain_comparisons_le xs.length xs.length (buildHeap xs.toArray).ret hsize.le
  rw [List.size_toArray] at hbuild hsum
  simp only [bottomUpHeapSort, time_bind, Prod.fst_add]
  rw [Nat.mul_add, Nat.mul_one]
  omega

end TimeM

end Cslib.Algorithms.Lean
