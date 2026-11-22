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

/-!
# Binary-heap sift-up event bounds

The cost coordinates count value comparisons and actual swaps, respectively.
Bounds checks, reads, copying, allocation, calls, and comparator implementation costs are free
in this model. These are execution-linked event bounds, not physical running-time bounds.
The canonical heap representation and operations are unchanged.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

/-- **The heap parent is one level up.** For every natural number $i > 0$, the parent index
$p = \lfloor (i-1)/2 \rfloor$ satisfies
$\lfloor \log_2(p+1) \rfloor + 1 = \lfloor \log_2(i+1) \rfloor$; that is, in the level-order
binary tree the parent of a nonroot index lies one level above it. -/
theorem log2_heapParent_add_one (i : Nat) (hi : 0 < i) :
    Nat.log2 (heapParent i + 1) + 1 = Nat.log2 (i + 1) := by
  rw [Nat.log2_def (i + 1)]
  split
  · congr 2
    unfold heapParent
    omega
  · omega

namespace TimeM

/-- **Sift-up with comparison and swap counts.** Given an array $a$ of length $|a|$ over a
linearly ordered type and an index $i$, this computes the sift-up of $a$ at $i$ together
with a cost $(c, s) \in \mathbb{N} \times \mathbb{N}$, where $c$ counts value comparisons
and $s$ counts swaps. If $i \ge |a|$ or $i = 0$, the result is $a$ with cost $(0, 0)$.
Otherwise let $p = \lfloor (i - 1)/2 \rfloor$ be the parent of $i$. If $a_i < a_p$, the
result is this sift-up at $p$ of the array obtained from $a$ by exchanging the entries at
positions $i$ and $p$, with cost $(1, 1)$ plus the cost of that recursive sift-up;
otherwise the result is $a$ with cost $(1, 0)$. -/
def siftUp {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    TimeM (Nat × Nat) (Array α) :=
  if hi : i < a.size then
    if hpos : 0 < i then do
      tick (1, 0)
      let p := heapParent i
      if a[i] < a[p]'(heapParent_lt_size a i hi hpos) then do
        tick (0, 1)
        siftUp (a.swap i p hi (heapParent_lt_size a i hi hpos)) p
      else
        pure a
    else
      pure a
  else
    pure a
termination_by i
decreasing_by
  unfold heapParent
  omega

/-- **Counting does not change the result of sift-up.** For every array $a$ over a linearly
ordered type and every natural number $i$, the array returned by sift-up with comparison and
swap counts on $a$ at index $i$ equals the array returned by the plain sift-up of $a$ at $i$. -/
theorem ret_siftUp {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    (siftUp a i).ret = Cslib.Algorithms.Lean.siftUp a i := by
  induction i using Nat.strong_induction_on generalizing a with
  | h i ih =>
    rw [siftUp, Cslib.Algorithms.Lean.siftUp]
    split
    · split
      · dsimp only
        simp only [ret_bind]
        split
        · simpa only [ret_bind, ret_tick] using
            ih (heapParent i) (by unfold heapParent; omega) _
        · rfl
      · rfl
    · rfl

/-- **Comparison bound for sift-up.** For every array $a$ over a linearly ordered type and
every natural number $i$, the number of value comparisons counted by sift-up with comparison
and swap counts on $a$ at index $i$ is at most $\lfloor \log_2(i+1) \rfloor$, the depth of
index $i$ in the level-order binary tree. -/
theorem comparisons_siftUp_le_log2 {α : Type u} [LinearOrder α]
    (a : Array α) (i : Nat) : (siftUp a i).time.1 ≤ Nat.log2 (i + 1) := by
  induction i using Nat.strong_induction_on generalizing a with
  | h i ih =>
    rw [siftUp]
    split
    · split
      · dsimp only
        simp only [time_bind]
        split
        · have hparent : heapParent i < i := by unfold heapParent; omega
          have hb := ih (heapParent i) hparent
            (a.swap i (heapParent i) ‹i < a.size› (heapParent_lt_size a i ‹_› ‹_›))
          have hd := log2_heapParent_add_one i ‹0 < i›
          simp at hb ⊢
          omega
        · have hd := log2_heapParent_add_one i ‹0 < i›
          simp
          omega
      · simp
    · simp

/-- **Swap bound for sift-up.** For every array $a$ over a linearly ordered type and every
natural number $i$, the number of swaps counted by sift-up with comparison and swap counts
on $a$ at index $i$ is at most $\lfloor \log_2(i+1) \rfloor$, the depth of index $i$ in the
level-order binary tree. -/
theorem swaps_siftUp_le_log2 {α : Type u} [LinearOrder α]
    (a : Array α) (i : Nat) : (siftUp a i).time.2 ≤ Nat.log2 (i + 1) := by
  induction i using Nat.strong_induction_on generalizing a with
  | h i ih =>
    rw [siftUp]
    split
    · split
      · dsimp only
        simp only [time_bind]
        split
        · have hparent : heapParent i < i := by unfold heapParent; omega
          have hb := ih (heapParent i) hparent
            (a.swap i (heapParent i) ‹i < a.size› (heapParent_lt_size a i ‹_› ‹_›))
          have hd := log2_heapParent_add_one i ‹0 < i›
          simp at hb ⊢
          omega
        · simp
      · simp
    · simp

/-- **Combined comparison and swap bound for sift-up.** For every array $a$ over a linearly
ordered type and every natural number $i$, if sift-up with comparison and swap counts on $a$
at index $i$ counts $c$ comparisons and $s$ swaps, then
$c + s \le 2 \lfloor \log_2(i+1) \rfloor$. -/
theorem events_siftUp_le_log2 {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    (siftUp a i).time.1 + (siftUp a i).time.2 ≤ 2 * Nat.log2 (i + 1) := by
  have hc := comparisons_siftUp_le_log2 a i
  have hs := swaps_siftUp_le_log2 a i
  omega

/-- **Sift-up at the root costs nothing.** For every array $a$ over a linearly ordered type,
sift-up with comparison and swap counts on $a$ at index $0$ has cost $(0, 0)$: it counts no
comparisons and no swaps. -/
theorem time_siftUp_zero {α : Type u} [LinearOrder α] (a : Array α) :
    (siftUp a 0).time = (0, 0) := by
  rw [siftUp]
  split <;> rfl

/-- **Sift-up at an out-of-range index costs nothing.** For every array $a$ of length $|a|$
over a linearly ordered type and every natural number $i$ with $i \ge |a|$, sift-up with
comparison and swap counts on $a$ at index $i$ has cost $(0, 0)$: it counts no comparisons
and no swaps. -/
theorem time_siftUp_of_size_le {α : Type u} [LinearOrder α] (a : Array α) (i : Nat)
    (hi : a.size ≤ i) : (siftUp a i).time = (0, 0) := by
  rw [siftUp]
  split
  · omega
  · rfl

end TimeM

end Cslib.Algorithms.Lean
