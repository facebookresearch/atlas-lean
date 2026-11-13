/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Tactic.Attr.Core
public import Batteries.Data.BinaryHeap.Basic
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Nat.Defs
import all Batteries.Data.BinaryHeap.Basic
import all Batteries.Data.BinaryHeap.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Counted bottom-up construction of the Batteries binary heap

`TimeM.heapifyDown` and `TimeM.mkHeap` instrument the canonical Batteries max-heap,
not the CSLibExt min-heap or its repeated-insertion heap sort. Erasure is exact for
arbitrary `Ord` comparators; no heap-order or comparator-law assumption is needed.

The two counters are `(value comparisons, vector swaps)`. Every call to `compare`
and every executed `Vector.swap` costs one in its respective component. Index
arithmetic, bounds checks, reads, pattern matching, recursive calls, comparator
internals, and vector copying are unpriced. These are abstract operation counts,
not CPU, bit, or Turing-machine time.

The build bound sums remaining *depth differences*. It is not the sum of actual
subtree heights. The former sum is bounded by twice the vector size, giving at
most six events per input element, including empty and singleton vectors.

The instrumented branch structure follows `Batteries.Data.BinaryHeap.Basic`;
its return proofs reuse the canonical lemmas in `Batteries.Data.BinaryHeap.Lemmas`.
The TimeM instrumentation style follows `BinaryHeap.SiftDownCost`.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.TimeM

set_option autoImplicit false

universe u

variable {α : Type u} [Ord α] {size : Nat}

/-- Canonical maximum-child selection, charging only the two-child comparison. -/
def timedMaxChild (a : Vector α size) (i : Fin size) :
    TimeM (Nat × Nat) (Option (Fin size)) :=
  let left := 2 * i.val + 1
  let right := left + 1
  if hleft : left < size then
    if hright : right < size then do
      tick (1, 0)
      pure (if (compare a[left] a[right]).isLT then
        some ⟨right, hright⟩ else some ⟨left, hleft⟩)
    else pure (some ⟨left, hleft⟩)
  else pure none

/-- Erasure of counted child selection is the canonical Batteries selector. -/
@[simp]
theorem ret_timedMaxChild (a : Vector α size) (i : Fin size) :
    (timedMaxChild a i).ret = Batteries.BinaryHeap.maxChild a i := by
  unfold timedMaxChild Batteries.BinaryHeap.maxChild
  dsimp only
  split
  · split <;> rfl
  · rfl

/-- Exactly one value comparison is charged iff the right child exists. -/
theorem time_timedMaxChild (a : Vector α size) (i : Fin size) :
    (timedMaxChild a i).time =
      if 2 * i.val + 2 < size then (1, 0) else (0, 0) := by
  unfold timedMaxChild
  dsimp only
  split
  · split <;> rfl
  · have hright : ¬2 * i.val + 2 < size := by omega
    simp [hright]
    rfl

/-- No child means no selector comparison and no swap. -/
theorem time_timedMaxChild_of_none (a : Vector α size) (i : Fin size)
    (h : Batteries.BinaryHeap.maxChild a i = none) :
    (timedMaxChild a i).time = (0, 0) := by
  have hleft := Batteries.BinaryHeap.maxChild_none_iff.mp h
  rw [time_timedMaxChild, ite_eq_right (by omega)]

/-- Canonical sift-down with one tick per comparator call and executed swap. -/
def heapifyDown (a : Vector α size) (i : Fin size) :
    TimeM (Nat × Nat) (Vector α size) :=
  let selected := timedMaxChild a i
  match hchild : selected.ret with
  | none => ⟨a, selected.time⟩
  | some j =>
    have hcanonical : Batteries.BinaryHeap.maxChild a i = some j :=
      (ret_timedMaxChild a i).symm.trans hchild
    have hij : i < j := Batteries.BinaryHeap.maxChild_gt hcanonical
    let run : TimeM (Nat × Nat) (Vector α size) := do
      tick (1, 0)
      if (compare a[i] a[j]).isLT then
        tick (0, 1)
        heapifyDown (a.swap i j) j
      else pure a
    ⟨run.ret, selected.time + run.time⟩
termination_by size - i.val
decreasing_by
  have := j.isLt
  omega

/-- A leaf returns unchanged and performs no events. -/
theorem heapifyDown_eq_of_maxChild_none (a : Vector α size) (i : Fin size)
    (h : Batteries.BinaryHeap.maxChild a i = none) :
    heapifyDown a i = ⟨a, (0, 0)⟩ := by
  rw [heapifyDown]
  dsimp only
  split
  · exact congrArg (fun cost => (⟨a, cost⟩ : TimeM (Nat × Nat) (Vector α size)))
      (time_timedMaxChild_of_none a i h)
  · rename_i j hj
    have hc := (ret_timedMaxChild a i).symm.trans hj
    rw [h] at hc
    cases hc

/-- The swap branch charges the selected-child comparison, parent comparison, and swap,
then continues on exactly the canonical swapped vector and child index. -/
theorem heapifyDown_eq_of_lt_child (a : Vector α size) (i j : Fin size)
    (hchild : Batteries.BinaryHeap.maxChild a i = some j)
    (hlt : (compare a[i] a[j]).isLT) :
    heapifyDown a i =
      ⟨(heapifyDown (a.swap i j) j).ret,
        (timedMaxChild a i).time + (1, 1) + (heapifyDown (a.swap i j) j).time⟩ := by
  rw [heapifyDown]
  dsimp only
  split
  · rename_i hn
    have hc := (ret_timedMaxChild a i).symm.trans hn
    rw [hchild] at hc
    cases hc
  · rename_i k hk
    have hc := (ret_timedMaxChild a i).symm.trans hk
    have hkj : k = j := Option.some.inj (hc.symm.trans hchild)
    subst k
    apply TimeM.ext
    · simp only [ret_bind, hlt, ↓reduceIte]
    · apply Prod.ext <;>
        simp only [time_bind, time_tick, hlt, ↓reduceIte, Prod.fst_add, Prod.snd_add] <;> omega

/-- A failed parent-child comparison stops without a swap. -/
theorem heapifyDown_eq_of_not_lt_child (a : Vector α size) (i j : Fin size)
    (hchild : Batteries.BinaryHeap.maxChild a i = some j)
    (hlt : ¬(compare a[i] a[j]).isLT) :
    heapifyDown a i = ⟨a, (timedMaxChild a i).time + (1, 0)⟩ := by
  rw [heapifyDown]
  dsimp only
  split
  · rename_i hn
    have hc := (ret_timedMaxChild a i).symm.trans hn
    rw [hchild] at hc
    cases hc
  · rename_i k hk
    have hc := (ret_timedMaxChild a i).symm.trans hk
    have hkj : k = j := Option.some.inj (hc.symm.trans hchild)
    subst k
    apply TimeM.ext
    · simp only [ret_bind, ite_eq_right hlt, ret_pure]
    · simp only [time_bind, time_tick, ite_eq_right hlt, time_pure, add_zero]

/-- Erasing the counters gives canonical sift-down on every valid vector/index. -/
@[simp]
theorem ret_heapifyDown (a : Vector α size) (i : Fin size) :
    (heapifyDown a i).ret = Batteries.BinaryHeap.heapifyDown a i := by
  induction a, i using Batteries.BinaryHeap.heapifyDown.induct with
  | case1 a i hchild =>
    rw [heapifyDown_eq_of_maxChild_none a i hchild,
      Batteries.BinaryHeap.heapifyDown_eq_of_maxChild_none hchild]
  | case2 a i j hchild _ hlt ih =>
    rw [heapifyDown_eq_of_lt_child a i j hchild hlt,
      Batteries.BinaryHeap.heapifyDown_eq_of_lt_child hchild hlt]
    exact ih
  | case3 a i j hchild _ hlt =>
    rw [heapifyDown_eq_of_not_lt_child a i j hchild hlt,
      Batteries.BinaryHeap.heapifyDown_eq_of_not_lt_child hchild hlt]

private theorem log2_maxChild_add_one (a : Vector α size) (i j : Fin size)
    (hchild : Batteries.BinaryHeap.maxChild a i = some j) :
    Nat.log2 (j.val + 1) = Nat.log2 (i.val + 1) + 1 := by
  have hshape := Batteries.BinaryHeap.maxChild_isChild hchild
  have hdiv : (j.val + 1) / 2 = i.val + 1 := by omega
  rw [Nat.log2_def (j.val + 1), ite_eq_left (by omega), hdiv]

/-- Total sift-down events are at most three per remaining binary-tree level. -/
theorem heapifyDown_time_le (a : Vector α size) (i : Fin size) :
    (heapifyDown a i).time.1 + (heapifyDown a i).time.2 ≤
      3 * (Nat.log2 size - Nat.log2 (i.val + 1)) := by
  induction a, i using Batteries.BinaryHeap.heapifyDown.induct with
  | case1 a i hchild =>
    rw [heapifyDown_eq_of_maxChild_none a i hchild]
    exact Nat.zero_le _
  | case2 a i j hchild _ hlt ih =>
    have hd := log2_maxChild_add_one a i j hchild
    have hn : Nat.log2 (j.val + 1) ≤ Nat.log2 size := by
      exact (Nat.le_log2 (by omega)).mpr
        ((Nat.log2_self_le (by omega : j.val + 1 ≠ 0)).trans (by omega))
    rw [heapifyDown_eq_of_lt_child a i j hchild hlt, time_timedMaxChild]
    split <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega
  | case3 a i j hchild _ hlt =>
    have hd := log2_maxChild_add_one a i j hchild
    have hn : Nat.log2 (j.val + 1) ≤ Nat.log2 size := by
      exact (Nat.le_log2 (by omega)).mpr
        ((Nat.log2_self_le (by omega : j.val + 1 ≠ 0)).trans (by omega))
    rw [heapifyDown_eq_of_not_lt_child a i j hchild hlt, time_timedMaxChild]
    split <;> simp only [Prod.fst_add, Prod.snd_add] <;> omega

/-- Counted canonical bottom-up build, visiting `size / 2 - 1, ..., 0`. -/
def mkHeap (a : Vector α size) : TimeM (Nat × Nat) (Vector α size) :=
  loop (size / 2) a (Nat.div_le_self ..)
where
  /-- Descending build loop, carrying the actual returned vector between sift-down calls. -/
  loop : (n : Nat) → Vector α size → n ≤ size → TimeM (Nat × Nat) (Vector α size)
    | 0, a, _ => pure a
    | n + 1, a, h => do
      let a' ← heapifyDown a ⟨n, Nat.lt_of_succ_le h⟩
      loop n a' (Nat.le_trans (Nat.le_succ _) h)

/-- Erasure of every descending-loop prefix is the canonical Batteries loop. -/
@[simp]
private theorem ret_mkHeap_loop (n : Nat) (a : Vector α size) (h : n ≤ size) :
    (mkHeap.loop n a h).ret = Batteries.BinaryHeap.mkHeap.loop n a h := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [mkHeap.loop, ret_bind, ret_heapifyDown, ih, Batteries.BinaryHeap.mkHeap.loop]

/-- Exact erasure to Batteries bottom-up construction; canonical correctness lemmas apply. -/
@[simp]
theorem ret_mkHeap (a : Vector α size) :
    (mkHeap a).ret = Batteries.BinaryHeap.mkHeap a := by
  exact ret_mkHeap_loop _ a _

private theorem mkHeap_loop_time_le (n : Nat) (a : Vector α size) (h : n ≤ size) :
    (mkHeap.loop n a h).time.1 + (mkHeap.loop n a h).time.2 ≤
      3 * ∑ i ∈ Finset.range n, (Nat.log2 size - Nat.log2 (i + 1)) := by
  induction n generalizing a with
  | zero => simp [mkHeap.loop]
  | succ n ih =>
    have hs := heapifyDown_time_le a ⟨n, Nat.lt_of_succ_le h⟩
    dsimp only at hs
    have hr := ih (heapifyDown a ⟨n, Nat.lt_of_succ_le h⟩).ret
      (Nat.le_trans (Nat.le_succ _) h)
    simp only [mkHeap.loop, time_bind, Prod.fst_add, Prod.snd_add, Finset.sum_range_succ]
    omega

private theorem sum_cutoff_le (m p : Nat) :
    (∑ i ∈ Finset.range m, if i < p then (1 : Nat) else 0) ≤ p := by
  rw [← Finset.card_filter]
  have hsub : (Finset.range m).filter (fun i => i < p) ⊆ Finset.range p := by
    intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  simpa only [Finset.card_range] using Finset.card_le_card hsub

-- A geometric bound uniform in the prefix length avoids identifying depth differences
-- with subtree heights. The additional level is supported on fewer than 2^(level+1) indices.
private theorem sum_depth_diff_add_two_le (level m : Nat) :
    (∑ i ∈ Finset.range m, (level - Nat.log2 (i + 1))) + 2 ≤ 2 ^ (level + 1) := by
  induction level with
  | zero => simp
  | succ level ih =>
    have hterm (i : Nat) :
        level + 1 - Nat.log2 (i + 1) ≤
          (level - Nat.log2 (i + 1)) + if i < 2 ^ (level + 1) then 1 else 0 := by
      split
      · omega
      · have hl : level + 1 ≤ Nat.log2 (i + 1) :=
          (Nat.le_log2 (by omega)).mpr (by omega)
        omega
    have hsum := Finset.sum_le_sum (s := Finset.range m) (fun i _ => hterm i)
    rw [Finset.sum_add_distrib] at hsum
    have hcut := sum_cutoff_le m (2 ^ (level + 1))
    rw [pow_succ (2 : Nat) (level + 1)]
    omega

private theorem sum_build_depth_diff_le (size : Nat) :
    (∑ i ∈ Finset.range (size / 2), (Nat.log2 size - Nat.log2 (i + 1))) ≤ 2 * size := by
  by_cases hzero : size = 0
  · simp [hzero]
  · have hsum := sum_depth_diff_add_two_le (Nat.log2 size) (size / 2)
    have hpow := Nat.log2_self_le hzero
    rw [pow_succ] at hsum
    omega

/-- Bottom-up construction uses at most `6 * size` comparisons and swaps in total.
This includes size zero and does not assume comparator laws or initial heap order. -/
theorem mkHeap_time_le (a : Vector α size) :
    (mkHeap a).time.1 + (mkHeap a).time.2 ≤ 6 * size := by
  have hloop := mkHeap_loop_time_le (size / 2) a (Nat.div_le_self ..)
  have hsum := sum_build_depth_diff_le size
  change (mkHeap.loop (size / 2) a (Nat.div_le_self ..)).time.1 +
    (mkHeap.loop (size / 2) a (Nat.div_le_self ..)).time.2 ≤ 6 * size
  omega

end Cslib.Algorithms.Lean.TimeM
