/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Prod

/-! # One-pass sift-down event costs

The counters record value comparisons and actual array swaps, not elapsed time.
Erasing counters gives canonical sift-down without a heap-order precondition.
Bounds use the remaining depth `Nat.log2 a.size - Nat.log2 (i + 1)`.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

set_option autoImplicit false

universe u

/-- **The smaller child lies one level below its parent.** Let $a$ be an array over a linearly
ordered type and let $i$ and $c$ be natural numbers. If $c$ is the smaller child of $i$ in $a$,
then $\lfloor \log_2 (c+1) \rfloor = \lfloor \log_2 (i+1) \rfloor + 1$; that is, in the
level-order binary tree stored in $a$, the node $c$ lies exactly one level below $i$. -/
theorem log2_smallerChild_add_one {α : Type u} [LinearOrder α]
    (a : Array α) (i c : Nat) (hchild : smallerChild a i = some c) :
    Nat.log2 (c + 1) = Nat.log2 (i + 1) + 1 := by
  have hgt := smallerChild_gt a i c hchild
  have hdiv : (c + 1) / 2 = i + 1 := by
    unfold smallerChild at hchild
    split at hchild
    · split at hchild
      · split at hchild <;> cases hchild <;> simp only [heapLeft, heapRight] <;> omega
      · cases hchild
        simp only [heapLeft]
        omega
    · cases hchild
  rw [Nat.log2_def (c + 1)]
  split
  · rw [hdiv]
  · omega

/-- **The smaller child's level is bounded by the array size.** Let $a$ be an array over a
linearly ordered type, of size $|a|$, and let $i$ and $c$ be natural numbers. If $c$ is the
smaller child of $i$ in $a$, then $\lfloor \log_2 (c+1) \rfloor \le \lfloor \log_2 |a| \rfloor$. -/
theorem log2_smallerChild_le_size {α : Type u} [LinearOrder α]
    (a : Array α) (i c : Nat) (hchild : smallerChild a i = some c) :
    Nat.log2 (c + 1) ≤ Nat.log2 a.size := by
  have hc := smallerChild_valid a i c hchild
  have hpow := (Nat.le_log2 (by omega : c + 1 ≠ 0)).mp
    (show Nat.log2 (c + 1) ≤ Nat.log2 (c + 1) from le_rfl)
  exact (Nat.le_log2 (by omega : a.size ≠ 0)).mpr (hpow.trans (by omega))

namespace TimeM

/-- **Timed smaller-child selection.** Let $a$ be an array over a linearly ordered type and $i$
an index, with left child $2i + 1$ and right child $2i + 2$; cost is counted as the pair
(value comparisons, array swaps). If both children are valid indices of $a$, the selection costs
$(1, 0)$ and returns the right child when its value is strictly less than the value at the left
child, and the left child otherwise. If only the left child is a valid index, it returns the
left child at cost $(0, 0)$. If the left child is not a valid index, it returns no child at cost
$(0, 0)$. -/
def timedSmallerChild {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    TimeM (Nat × Nat) (Option Nat) :=
  if hl : heapLeft i < a.size then
    if hr : heapRight i < a.size then do
      tick (1, 0)
      pure (if a[heapRight i] < a[heapLeft i] then
        some (heapRight i) else some (heapLeft i))
    else pure (some (heapLeft i))
  else pure none

/-- **Timed child selection returns the smaller child.** For every array $a$ over a linearly
ordered type and every index $i$, the value returned by timed child selection at $i$, with its
cost discarded, is the smaller child of $i$ in $a$ (an optional index, absent when $i$ has no
valid child). -/
theorem ret_timedSmallerChild {α : Type u} [LinearOrder α]
    (a : Array α) (i : Nat) :
    (timedSmallerChild a i).ret = smallerChild a i := by
  unfold timedSmallerChild smallerChild
  split <;> rename_i hl
  · split <;> rfl
  · rfl

/-- **Sift-down with comparison and swap counts.** For an array $a$ over a linearly ordered
type and an index $i$, timed sift-down returns an array together with a cost pair
(value comparisons, array swaps), where costs add componentwise. If the left child index
$2i+1$ is not a valid index of $a$, it returns $a$ at cost $(0, 0)$. Otherwise let $c$ be the
smaller child of $i$: the left child $2i+1$, unless the right child $2i+2$ is a valid index
and $a_{2i+2} < a_{2i+1}$, in which case $c = 2i+2$. Selecting $c$ costs one comparison when
$2i+2$ is a valid index and nothing otherwise. Comparing $a_c$ with $a_i$ costs one more
comparison. If $a_c < a_i$, the entries at $i$ and $c$ are swapped at the cost of one swap,
and the result and remaining cost are those of timed sift-down from $c$ in the swapped array;
otherwise the result is $a$.

Index arithmetic, bounds checks, pattern matching and recursive calls are free. -/
def siftDown {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    TimeM (Nat × Nat) (Array α) :=
  let selected := timedSmallerChild a i
  match hchild : selected.ret with
  | none => ⟨a, selected.time⟩
  | some c =>
    have hcanonical : smallerChild a i = some c :=
      (ret_timedSmallerChild a i).symm.trans hchild
    have hc : c < a.size := smallerChild_valid a i c hcanonical
    have hi : i < a.size := (smallerChild_gt a i c hcanonical).trans hc
    let run : TimeM (Nat × Nat) (Array α) := do
      tick (1, 0)
      if hlt : a[c] < a[i] then
        tick (0, 1)
        siftDown (a.swap i c hi hc) c
      else pure a
    ⟨run.ret, selected.time + run.time⟩
termination_by a.size - i
decreasing_by
  simp only [Array.size_swap]
  have := smallerChild_gt a i c hcanonical
  omega

/-- **Timed sift-down returns the sift-down result.** For every array $a$ over a linearly
ordered type and every index $i$, the array returned by timed sift-down from $i$, with its
cost discarded, equals the array returned by sift-down from $i$. -/
theorem ret_siftDown {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    (siftDown a i).ret = Cslib.Algorithms.Lean.siftDown a i := by
  induction hm : a.size - i using Nat.strong_induction_on generalizing a i with
  | h n ih =>
    rw [siftDown, Cslib.Algorithms.Lean.siftDown]
    dsimp only
    split
    · rename_i hnone
      have hn : smallerChild a i = none := (ret_timedSmallerChild a i).symm.trans hnone
      split
      · rfl
      · rename_i c hs
        simp only [hn] at hs
        cases hs
    · rename_i c hselected
      have hchild : smallerChild a i = some c :=
        (ret_timedSmallerChild a i).symm.trans hselected
      dsimp only
      simp only [ret_bind]
      split
      · have hc := smallerChild_valid a i c hchild
        have hi := (smallerChild_gt a i c hchild).trans hc
        have hdec : (a.swap i c hi hc).size - c < n := by
          simp only [Array.size_swap]
          rw [← hm]
          have := smallerChild_gt a i c hchild
          omega
        have hih := ih _ hdec (a.swap i c hi hc) c rfl
        simp only [ret_bind]
        split
        · rename_i hn
          simp only [hchild] at hn
          cases hn
        · rename_i d hd
          have hcd : some c = some d := hchild.symm.trans hd
          cases hcd
          split
          · exact hih
          · contradiction
      · split
        · rename_i hn
          simp only [hchild] at hn
          cases hn
        · rename_i d hd
          have hcd : some c = some d := hchild.symm.trans hd
          cases hcd
          split
          · contradiction
          · rfl

/-- **Cost of child selection.** Let $a$ be an array over a linearly ordered type and $i$ an
index, and count cost as the pair (value comparisons, array swaps). The timed child selection at
$i$ in $a$ has cost $(1, 0)$ if the right child index $2i + 2$ is less than the size of $a$, and
cost $(0, 0)$ otherwise. -/
theorem time_timedSmallerChild {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    (timedSmallerChild a i).time =
      if heapRight i < a.size then (1, 0) else (0, 0) := by
  unfold timedSmallerChild
  split
  · split <;> rfl
  · have hr : ¬heapRight i < a.size := by
      unfold heapLeft heapRight at *
      omega
    simp [hr]
    rfl

/-- **Child selection at a node without children costs nothing.** Let $a$ be an array over a
linearly ordered type and $i$ an index. If the smaller-child selection at $i$ in $a$ returns no
child, then the timed child selection at $i$, with cost counted as the pair (value comparisons,
array swaps), has cost $(0, 0)$. -/
theorem time_timedSmallerChild_of_none {α : Type u} [LinearOrder α]
    (a : Array α) (i : Nat) (hchild : smallerChild a i = none) :
    (timedSmallerChild a i).time = (0, 0) := by
  unfold smallerChild at hchild
  split at hchild
  · split at hchild
    · split at hchild <;> cases hchild
    · cases hchild
  · unfold timedSmallerChild
    split
    · contradiction
    · rfl

/-- **Sift-down performs at most one swap per remaining level.** Write $|a|$ for the size of an
array $a$, and let $\ell(n) = \lfloor \log_2 n \rfloor$ for $n \ge 1$ and $\ell(0) = 0$. For
every array $a$ over a linearly ordered type and every index $i$, the number of array swaps
counted by timed sift-down from $i$ is at most $\max(0, \ell(|a|) - \ell(i+1))$. -/
theorem siftDown_swaps_le {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    (siftDown a i).time.2 ≤ Nat.log2 a.size - Nat.log2 (i + 1) := by
  induction hm : a.size - i using Nat.strong_induction_on generalizing a i with
  | h n ih =>
    rw [siftDown]
    dsimp only
    split
    · rename_i hnone
      have hn : smallerChild a i = none := (ret_timedSmallerChild a i).symm.trans hnone
      rw [time_timedSmallerChild_of_none a i hn]
      simp
    · rename_i c hselected
      have hchild : smallerChild a i = some c :=
        (ret_timedSmallerChild a i).symm.trans hselected
      have hs : (timedSmallerChild a i).time.2 = 0 := by
        rw [time_timedSmallerChild]
        split <;> rfl
      dsimp only
      simp only [time_bind]
      split
      · have hc := smallerChild_valid a i c hchild
        have hi := (smallerChild_gt a i c hchild).trans hc
        have hdec : (a.swap i c hi hc).size - c < n := by
          simp only [Array.size_swap]
          rw [← hm]
          have := smallerChild_gt a i c hchild
          omega
        have hb := ih _ hdec (a.swap i c hi hc) c rfl
        have hd := log2_smallerChild_add_one a i c hchild
        have hn := log2_smallerChild_le_size a i c hchild
        simp [hs] at hb ⊢
        omega
      · simp [hs]

/-- **Sift-down makes at most two comparisons per remaining level.** Write $|a|$ for the size
of an array $a$, and let $\ell(n) = \lfloor \log_2 n \rfloor$ for $n \ge 1$ and $\ell(0) = 0$.
For every array $a$ over a linearly ordered type and every index $i$, the number of value
comparisons counted by timed sift-down from $i$ is at most $2 \max(0, \ell(|a|) - \ell(i+1))$. -/
theorem siftDown_comparisons_le {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    (siftDown a i).time.1 ≤ 2 * (Nat.log2 a.size - Nat.log2 (i + 1)) := by
  induction hm : a.size - i using Nat.strong_induction_on generalizing a i with
  | h n ih =>
    rw [siftDown]
    dsimp only
    split
    · rename_i hnone
      have hn : smallerChild a i = none := (ret_timedSmallerChild a i).symm.trans hnone
      rw [time_timedSmallerChild_of_none a i hn]
      simp
    · rename_i c hselected
      have hchild : smallerChild a i = some c :=
        (ret_timedSmallerChild a i).symm.trans hselected
      have hs : (timedSmallerChild a i).time.1 ≤ 1 := by
        rw [time_timedSmallerChild]
        split <;> simp
      have hd := log2_smallerChild_add_one a i c hchild
      have hn := log2_smallerChild_le_size a i c hchild
      dsimp only
      simp only [time_bind]
      split
      · have hc := smallerChild_valid a i c hchild
        have hi := (smallerChild_gt a i c hchild).trans hc
        have hdec : (a.swap i c hi hc).size - c < n := by
          simp only [Array.size_swap]
          rw [← hm]
          have := smallerChild_gt a i c hchild
          omega
        have hb := ih _ hdec (a.swap i c hi hc) c rfl
        simp at hb ⊢
        omega
      · simp
        omega

/-- **Total sift-down cost is at most three per remaining level.** Write $|a|$ for the size of
an array $a$, and let $\ell(n) = \lfloor \log_2 n \rfloor$ for $n \ge 1$ and $\ell(0) = 0$.
For every array $a$ over a linearly ordered type and every index $i$, the number of value
comparisons plus the number of array swaps counted by timed sift-down from $i$ is at most
$3 \max(0, \ell(|a|) - \ell(i+1))$. -/
theorem siftDown_time_le {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    (siftDown a i).time.1 + (siftDown a i).time.2 ≤
      3 * (Nat.log2 a.size - Nat.log2 (i + 1)) := by
  have hc := siftDown_comparisons_le a i
  have hs := siftDown_swaps_le a i
  omega

/-- **Sift-down from a node without children costs nothing.** Let $a$ be an array over a
linearly ordered type and $i$ an index. If the smaller-child selection at $i$ in $a$ returns no
child, then sift-down from $i$, with cost counted as the pair (value comparisons, array swaps),
has cost $(0, 0)$: it makes no value comparisons and no array swaps. -/
theorem time_siftDown_of_smallerChild_none {α : Type u} [LinearOrder α]
    (a : Array α) (i : Nat) (hchild : smallerChild a i = none) :
    (siftDown a i).time = (0, 0) := by
  rw [siftDown]
  dsimp only
  split
  · exact time_timedSmallerChild_of_none a i hchild
  · rename_i c hs
    have hc : smallerChild a i = some c := (ret_timedSmallerChild a i).symm.trans hs
    rw [hchild] at hc
    cases hc

/-- **Sift-down from a leaf costs nothing.** Let $a$ be an array over a linearly ordered type,
of size $|a|$, and let $i$ be an index with $|a| \le 2i+1$, so that the left child of $i$ is not
a valid index (this includes invalid indices $i$). Then timed sift-down from $i$ has cost pair
$(0, 0)$: it counts no comparisons and no swaps. -/
theorem time_siftDown_of_heapLeft_ge {α : Type u} [LinearOrder α]
    (a : Array α) (i : Nat) (h : a.size ≤ heapLeft i) :
    (siftDown a i).time = (0, 0) := by
  apply time_siftDown_of_smallerChild_none
  unfold smallerChild
  split
  · omega
  · rfl

/-- **Sift-down from an invalid index costs nothing.** Let $a$ be an array over a linearly
ordered type, of size $|a|$, and let $i$ be a natural number with $|a| \le i$. Then timed
sift-down from $i$ has cost pair $(0, 0)$: it counts no comparisons and no swaps. -/
theorem time_siftDown_of_size_le {α : Type u} [LinearOrder α]
    (a : Array α) (i : Nat) (h : a.size ≤ i) :
    (siftDown a i).time = (0, 0) := by
  apply time_siftDown_of_heapLeft_ge
  unfold heapLeft
  omega

end TimeM

end Cslib.Algorithms.Lean
