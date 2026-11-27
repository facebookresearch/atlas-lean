/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap.SiftDownCost
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Bottom-up construction of a binary min-heap

`buildHeap` turns an arbitrary array into a binary min-heap by sifting down every internal
position, from the last one back to the root. `TimeM.buildHeap` instruments it with the
`(value comparisons, array swaps)` counters of `TimeM.siftDown`; erasing the counters gives
`buildHeap`.

The cost is measured against node heights in the level-order tree, `heapHeight n i`, rather
than against the remaining depth `Nat.log2 n - Nat.log2 (i + 1)` that bounds a single
sift-down in `BinaryHeap.SiftDownCost`: the heights of an `n`-node tree sum to exactly
`n` minus the binary digit sum of `n`, which makes the linear bound explicit.

The construction is the first pass of R. W. Floyd's *Algorithm 245: Treesort 3*
(Comm. ACM 7(12), 701, 1964), with the root included, written here for a min-heap indexed from
`0`. The analysis by the sum of node heights, and the exact sum `2^(h+1) - 1 - (h+1)` for a
perfect tree of height `h`, follow C. Zander's course notes *Linear heap algorithm (buildheap)*
(CSS 343, University of Washington Bothell).
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

set_option autoImplicit false

universe u

/-! ### Node heights -/

/-- **Height of a node in a level-order binary tree.** For natural numbers $n$ and $i$, the height
of the index $i$ in the binary tree with $n$ nodes stored in level order at the indices
$0, \dots, n - 1$ is $\lfloor \log_2 \lfloor n/(i+1) \rfloor \rfloor$, where
$\lfloor \log_2 0 \rfloor$ is read as $0$. For $i < n$ this is the largest $d$ with
$(i+1) 2^d \le n$, and for $i \ge n$ it is $0$. -/
def heapHeight (n i : Nat) : Nat := Nat.log 2 (n / (i + 1))

-- For a valid index, `d ≤ heapHeight n i` exactly when `(i + 1) * 2 ^ d ≤ n`.
theorem le_heapHeight_iff {n i : Nat} (hi : i < n) (d : Nat) :
    d ≤ heapHeight n i ↔ (i + 1) * 2 ^ d ≤ n := by
  unfold heapHeight
  rw [Nat.le_log_iff_pow_le (by norm_num) (by
    rw [Ne, Nat.div_eq_zero_iff]
    omega), Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]

private theorem heapHeight_of_lt_two_mul {n i : Nat} (h : n < 2 * (i + 1)) :
    heapHeight n i = 0 := by
  unfold heapHeight
  apply Nat.log_of_lt
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  omega

private theorem heapHeight_eq_half_add_one {n i : Nat} (h : 2 * (i + 1) ≤ n) :
    heapHeight n i = heapHeight (n / 2) i + 1 := by
  unfold heapHeight
  have hdiv : n / 2 / (i + 1) = n / (i + 1) / 2 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  have hpos : 0 < Nat.log 2 (n / (i + 1)) :=
    Nat.log_pos (by norm_num) ((Nat.le_div_iff_mul_le (by omega)).mpr (by omega))
  rw [hdiv, Nat.log_div_base]
  omega

private theorem heapHeight_heapLeft (n i : Nat) :
    heapHeight n (heapLeft i) = heapHeight (n / 2) i := by
  unfold heapHeight heapLeft
  rw [Nat.div_div_eq_div_mul]
  congr 2

/-- **Height is one more than the taller child's height.** For all natural numbers $n$ and $i$,
in the level-order binary tree with $n$ nodes, if the left child $2i + 1$ of $i$ is a valid index
(that is, $2i + 1 < n$), then the height of $i$ is one more than the larger of the heights of its
children $2i + 1$ and $2i + 2$; otherwise the height of $i$ is $0$. Here an index $j \ge n$ has
height $0$. This is the recursion for the number of edges on a longest downward path from $i$ to
a leaf. -/
theorem heapHeight_eq (n i : Nat) :
    heapHeight n i = if heapLeft i < n then
      max (heapHeight n (heapLeft i)) (heapHeight n (heapRight i)) + 1 else 0 := by
  have hright : heapHeight n (heapRight i) ≤ heapHeight n (heapLeft i) := by
    unfold heapHeight heapLeft heapRight
    exact Nat.log_mono_right (Nat.div_le_div_left (by omega) (by omega))
  split
  · rw [max_eq_left hright, heapHeight_heapLeft]
    exact heapHeight_eq_half_add_one (by unfold heapLeft at *; omega)
  · exact heapHeight_of_lt_two_mul (by unfold heapLeft at *; omega)

/-- A valid child is at least one level lower than its parent. -/
private theorem heapHeight_add_one_le {n i c : Nat} (hc : heapLeft i ≤ c) (hcn : c < n) :
    heapHeight n c + 1 ≤ heapHeight n i := by
  have hmono : heapHeight n c ≤ heapHeight n (heapLeft i) := by
    unfold heapHeight
    exact Nat.log_mono_right (Nat.div_le_div_left (by omega) (by unfold heapLeft; omega))
  rw [heapHeight_heapLeft] at hmono
  rw [heapHeight_eq_half_add_one (n := n) (i := i) (by unfold heapLeft at hc; omega)]
  omega

/-- Halving recursion for the sum of all heights. -/
private theorem sum_heapHeight_eq_half (n : Nat) :
    ∑ i ∈ Finset.range n, heapHeight n i =
      n / 2 + ∑ i ∈ Finset.range (n / 2), heapHeight (n / 2) i := by
  have hsplit : n = n / 2 + (n - n / 2) := by omega
  rw [hsplit, Finset.sum_range_add, ← hsplit]
  have hupper : ∑ x ∈ Finset.range (n - n / 2), heapHeight n (n / 2 + x) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact heapHeight_of_lt_two_mul (by omega)
  have hlower : ∑ x ∈ Finset.range (n / 2), heapHeight n x =
      ∑ x ∈ Finset.range (n / 2), (heapHeight (n / 2) x + 1) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact heapHeight_eq_half_add_one (by rw [Finset.mem_range] at hx; omega)
  rw [hupper, hlower, Finset.sum_add_distrib, ← Finset.card_eq_sum_ones, Finset.card_range]
  omega

-- The heights of an `n`-node tree and the binary digits of `n` add up to `n`.
theorem sum_heapHeight_add_digits_sum (n : Nat) :
    ∑ i ∈ Finset.range n, heapHeight n i + (Nat.digits 2 n).sum = n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hhalf := ih (n / 2) (by omega)
      rw [sum_heapHeight_eq_half, Nat.digits_def' (by norm_num) hn, List.sum_cons]
      omega

private theorem digits_sum_two_pow_sub_one (k : Nat) :
    (Nat.digits 2 (2 ^ k - 1)).sum = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, Nat.mul_comm]
    have hk : 0 < 2 ^ k := Nat.two_pow_pos k
    rw [Nat.digits_def' (by norm_num) (by omega), List.sum_cons,
      show (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 by omega, ih]
    omega

/-! ### The construction -/

variable {α : Type u} [LinearOrder α]

/-- **Bottom-up heap construction.** For an array $a$ of length $n$ over a linearly ordered type,
bottom-up construction sifts down the positions $i = \lfloor n/2 \rfloor - 1, \dots, 1, 0$ in
turn, each time continuing with the array the previous sift-down returned. When $n \le 1$ there
is no such position and the result is $a$. -/
def buildHeap (a : Array α) : Array α :=
  loop (a.size / 2) a
where
  -- `loop k b` sifts down the positions `k - 1, ..., 1, 0` of `b` in turn.
  loop : Nat → Array α → Array α
    | 0, b => b
    | k + 1, b => loop k (siftDown b k)

private theorem buildHeap_loop_perm (k : Nat) (b : Array α) :
    (buildHeap.loop k b).Perm b := by
  induction k generalizing b with
  | zero => exact Array.Perm.refl _
  | succ k ih => exact (ih (siftDown b k)).trans (siftDown_perm b k)

-- Bottom-up heap construction permutes the array.
theorem buildHeap_perm (a : Array α) : (buildHeap a).Perm a :=
  buildHeap_loop_perm _ a

/-! ### Correctness

While the positions `k - 1, ..., 1, 0` remain to be sifted down, every edge whose parent index
is at least `k` is ordered. Sifting down from `k` restores this for the edges whose parent index
is `k`: during that sift-down, every edge with parent index at least `k` is ordered except those
leaving the moving entry's position `i`, and if `i > k` the entry above `i` is at most both
children of `i`. -/

@[simp] private theorem heapParent_heapLeft (i : Nat) : heapParent (heapLeft i) = i := by
  simp only [heapParent, heapLeft]
  omega

@[simp] private theorem heapParent_heapRight (i : Nat) : heapParent (heapRight i) = i := by
  simp only [heapParent, heapRight]
  omega

private theorem eq_heapLeft_or_heapRight {i j : Nat} (hjpos : 0 < j)
    (hp : heapParent j = i) : j = heapLeft i ∨ j = heapRight i := by
  simp only [heapParent] at hp
  simp only [heapLeft, heapRight]
  omega

private theorem smallerChild_some {a : Array α} {i c : Nat} (h : smallerChild a i = some c) :
    c = heapLeft i ∨ c = heapRight i := by
  unfold smallerChild at h
  split at h
  · split at h
    · split at h <;> cases h <;> simp
    · cases h
      simp
  · cases h

private theorem heapParent_of_smallerChild {a : Array α} {i c : Nat}
    (h : smallerChild a i = some c) : heapParent c = i := by
  rcases smallerChild_some h with rfl | rfl <;> simp

private theorem heapLeft_le_of_smallerChild {a : Array α} {i c : Nat}
    (h : smallerChild a i = some c) : heapLeft i ≤ c := by
  rcases smallerChild_some h with rfl | rfl <;> simp [heapLeft, heapRight]

private theorem size_le_heapLeft_of_smallerChild {a : Array α} {i : Nat}
    (h : smallerChild a i = none) : a.size ≤ heapLeft i := by
  unfold smallerChild at h
  split at h
  · split at h
    · split at h <;> cases h
    · cases h
  · omega

private theorem smallerChild_le_child {a : Array α} {i c : Nat}
    (h : smallerChild a i = some c) {j : Nat} (hj : j < a.size) (hjpos : 0 < j)
    (hp : heapParent j = i) : a[c]'(smallerChild_valid a i c h) ≤ a[j] := by
  unfold smallerChild at h
  split at h
  · split at h
    · split at h
      · cases h
        rcases eq_heapLeft_or_heapRight hjpos hp with rfl | rfl
        · exact le_of_lt ‹a[heapRight i] < a[heapLeft i]›
        · exact le_rfl
      · cases h
        rcases eq_heapLeft_or_heapRight hjpos hp with rfl | rfl
        · exact le_rfl
        · exact le_of_not_gt ‹¬a[heapRight i] < a[heapLeft i]›
    · cases h
      rcases eq_heapLeft_or_heapRight hjpos hp with rfl | rfl
      · exact le_rfl
      · omega
  · cases h

/-- Every edge whose parent index is at least `k` is ordered. -/
private def OrderedFrom (a : Array α) (k : Nat) : Prop :=
  ∀ j (hj : j < a.size) (hjpos : 0 < j), k ≤ heapParent j →
    a[heapParent j]'(heapParent_lt_size a j hj hjpos) ≤ a[j]

/-- The sift-down invariant at the moving index `i`, for the edges with parent at least `k`. -/
private structure SiftDownReadyFrom (a : Array α) (k i : Nat) : Prop where
  le_index : k ≤ i
  ordered_except : ∀ j (hj : j < a.size) (hjpos : 0 < j), k ≤ heapParent j →
    heapParent j ≠ i → a[heapParent j]'(heapParent_lt_size a j hj hjpos) ≤ a[j]
  parent_below_children : ∀ j (hj : j < a.size) (hjpos : 0 < j) (hp : heapParent j = i)
    (hki : k < i),
    a[heapParent i]'(by
      have := heapParent_lt j hjpos
      have := heapParent_lt i (by omega)
      omega) ≤ a[j]

private theorem siftDownReadyFrom_swap (a : Array α) (k i c : Nat)
    (hchild : smallerChild a i = some c) (h : SiftDownReadyFrom a k i)
    (hi : i < a.size)
    (hlt : a[c]'(smallerChild_valid a i c hchild) < a[i]) :
    SiftDownReadyFrom (a.swap i c hi (smallerChild_valid a i c hchild)) k c := by
  have hc : c < a.size := smallerChild_valid a i c hchild
  have hic : i < c := smallerChild_gt a i c hchild
  have hpci : heapParent c = i := heapParent_of_smallerChild hchild
  refine ⟨by have := h.le_index; omega, ?_, ?_⟩
  · intro j hj hjpos hkj hparentc
    have hja : j < a.size := by simpa using hj
    by_cases hjc : j = c
    · subst j
      simp [hpci, hlt.le]
    · by_cases hji : j = i
      · subst j
        have hold := h.parent_below_children c hc (by omega) hpci
          (by have := heapParent_lt i hjpos; omega)
        have hparent_ne_c : heapParent i ≠ c := by
          have := heapParent_lt i hjpos
          omega
        have hparent_ne_i : heapParent i ≠ i := (heapParent_lt i hjpos).ne
        rw [Array.getElem_swap_of_ne hparent_ne_i hparent_ne_c, Array.getElem_swap_left]
        exact hold
      · by_cases hparenti : heapParent j = i
        · have hold := smallerChild_le_child hchild hja hjpos hparenti
          simpa only [Array.getElem_swap, hparenti, hji, hjc, hic.ne, ite_true,
            ite_false] using hold
        · have hold := h.ordered_except j hja hjpos hkj hparenti
          rw [Array.getElem_swap_of_ne hparenti hparentc, Array.getElem_swap_of_ne hji hjc]
          exact hold
  · intro j hj hjpos hparent _
    have hja : j < a.size := by simpa using hj
    have hcj : c < j := by
      rw [← hparent]
      exact heapParent_lt j hjpos
    have hjc : j ≠ c := by omega
    have hji : j ≠ i := by omega
    have hold := h.ordered_except j hja hjpos (by rw [hparent]; have := h.le_index; omega)
      (by omega)
    have hold' : a[c]'hc ≤ a[j] := by simpa only [hparent] using hold
    simpa only [Array.getElem_swap, hpci, hji, hjc, hic.ne, ite_true, ite_false] using hold'

private theorem siftDown_orderedFrom (a : Array α) (k i : Nat) (h : SiftDownReadyFrom a k i) :
    OrderedFrom (siftDown a i) k := by
  induction hm : a.size - i using Nat.strong_induction_on generalizing a i with
  | ind n ih =>
    rw [siftDown]
    split
    · rename_i hnone
      have hleft := size_le_heapLeft_of_smallerChild hnone
      intro j hj hjpos hkj
      have hpi : heapParent j ≠ i := by
        intro hp
        rcases eq_heapLeft_or_heapRight hjpos hp with rfl | rfl <;>
          simp only [heapLeft, heapRight] at hleft hj <;> omega
      exact h.ordered_except j hj hjpos hkj hpi
    · rename_i c hchild
      dsimp only
      have hc := smallerChild_valid a i c hchild
      have hi := (smallerChild_gt a i c hchild).trans hc
      split
      · rename_i hlt
        have hready := siftDownReadyFrom_swap a k i c hchild h hi hlt
        have hdec : (a.swap i c hi hc).size - c < n := by
          simp only [Array.size_swap]
          have := smallerChild_gt a i c hchild
          omega
        exact ih _ hdec _ _ hready rfl
      · rename_i hnlt
        intro j hj hjpos hkj
        by_cases hp : heapParent j = i
        · have hbase := (le_of_not_gt hnlt).trans (smallerChild_le_child hchild hj hjpos hp)
          simpa only [hp] using hbase
        · exact h.ordered_except j hj hjpos hkj hp

private theorem buildHeap_loop_ordered (k : Nat) (b : Array α) (h : OrderedFrom b k) :
    HeapOrdered (buildHeap.loop k b) := by
  induction k generalizing b with
  | zero => exact fun j hj hjpos => h j hj hjpos (Nat.zero_le _)
  | succ k ih =>
    apply ih
    apply siftDown_orderedFrom
    refine ⟨le_rfl, ?_, ?_⟩
    · intro j hj hjpos hkj hne
      exact h j hj hjpos (by omega)
    · intro _ _ _ _ hkk
      omega

-- Bottom-up heap construction returns a heap-ordered array.
theorem buildHeap_ordered (a : Array α) : HeapOrdered (buildHeap a) := by
  apply buildHeap_loop_ordered
  intro j hj hjpos hkj
  simp only [heapParent] at hkj
  omega

/-! ### Counted construction -/

namespace TimeM

/-- **Bottom-up heap construction with comparison and swap counts.** For an array $a$ of length
$n$ over a linearly ordered type, the timed construction runs timed sift-down from the positions
$i = \lfloor n/2 \rfloor - 1, \dots, 1, 0$ in turn, each on the array the previous one returned,
and returns the last array together with the componentwise sum of their cost pairs
(value comparisons, array swaps). -/
def buildHeap (a : Array α) : TimeM (Nat × Nat) (Array α) :=
  loop (a.size / 2) a
where
  -- `loop k b` runs timed sift-down from the positions `k - 1, ..., 1, 0` of `b` in turn.
  loop : Nat → Array α → TimeM (Nat × Nat) (Array α)
    | 0, b => pure b
    | k + 1, b => do
      let b' ← siftDown b k
      loop k b'

private theorem ret_buildHeap_loop (k : Nat) (b : Array α) :
    (buildHeap.loop k b).ret = Lean.buildHeap.loop k b := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
    simp only [buildHeap.loop, ret_bind, ret_siftDown, ih, Lean.buildHeap.loop]

-- Erasing the counters of the timed construction gives bottom-up heap construction.
@[simp]
theorem ret_buildHeap (a : Array α) : (buildHeap a).ret = Lean.buildHeap a :=
  ret_buildHeap_loop _ a

private theorem size_ret_siftDown (b : Array α) (i : Nat) : (siftDown b i).ret.size = b.size := by
  rw [ret_siftDown]
  exact (siftDown_perm b i).size_eq

/-- **Sift-down performs at most as many swaps as the height of its start.** For every array $a$
over a linearly ordered type, of length $n$, and every index $i$, the number of array swaps
counted by timed sift-down from $i$ is at most the height of $i$ in the level-order binary tree
with $n$ nodes, $\lfloor \log_2 \lfloor n/(i+1) \rfloor \rfloor$ (which is $0$ when $i \ge n$). -/
theorem siftDown_swaps_le_heapHeight (a : Array α) (i : Nat) :
    (siftDown a i).time.2 ≤ heapHeight a.size i := by
  induction hm : a.size - i using Nat.strong_induction_on generalizing a i with
  | ind n ih =>
    rw [siftDown]
    dsimp only
    split
    · rename_i hnone
      have hn : smallerChild a i = none := (ret_timedSmallerChild a i).symm.trans hnone
      rw [time_timedSmallerChild_of_none a i hn]
      exact Nat.zero_le _
    · rename_i c hselected
      have hchild : smallerChild a i = some c :=
        (ret_timedSmallerChild a i).symm.trans hselected
      have hs : (timedSmallerChild a i).time.2 = 0 := by
        rw [time_timedSmallerChild]
        split <;> rfl
      have hc := smallerChild_valid a i c hchild
      have hheight := heapHeight_add_one_le (heapLeft_le_of_smallerChild hchild) hc
      dsimp only
      simp only [time_bind]
      split
      · have hi := (smallerChild_gt a i c hchild).trans hc
        have hdec : (a.swap i c hi hc).size - c < n := by
          simp only [Array.size_swap]
          have := smallerChild_gt a i c hchild
          omega
        have hb := ih _ hdec (a.swap i c hi hc) c rfl
        simp only [Array.size_swap] at hb
        simp [hs]
        omega
      · simp [hs]

/-- **Sift-down makes at most two comparisons per unit of height of its start.** For every array
$a$ over a linearly ordered type, of length $n$, and every index $i$, the number of value
comparisons counted by timed sift-down from $i$ is at most twice the height of $i$ in the
level-order binary tree with $n$ nodes, $2 \lfloor \log_2 \lfloor n/(i+1) \rfloor \rfloor$ (which
is $0$ when $i \ge n$). -/
theorem siftDown_comparisons_le_heapHeight (a : Array α) (i : Nat) :
    (siftDown a i).time.1 ≤ 2 * heapHeight a.size i := by
  induction hm : a.size - i using Nat.strong_induction_on generalizing a i with
  | ind n ih =>
    rw [siftDown]
    dsimp only
    split
    · rename_i hnone
      have hn : smallerChild a i = none := (ret_timedSmallerChild a i).symm.trans hnone
      rw [time_timedSmallerChild_of_none a i hn]
      exact Nat.zero_le _
    · rename_i c hselected
      have hchild : smallerChild a i = some c :=
        (ret_timedSmallerChild a i).symm.trans hselected
      have hs : (timedSmallerChild a i).time.1 ≤ 1 := by
        rw [time_timedSmallerChild]
        split <;> simp
      have hc := smallerChild_valid a i c hchild
      have hheight := heapHeight_add_one_le (heapLeft_le_of_smallerChild hchild) hc
      dsimp only
      simp only [time_bind]
      split
      · have hi := (smallerChild_gt a i c hchild).trans hc
        have hdec : (a.swap i c hi hc).size - c < n := by
          simp only [Array.size_swap]
          have := smallerChild_gt a i c hchild
          omega
        have hb := ih _ hdec (a.swap i c hi hc) c rfl
        simp only [Array.size_swap] at hb
        simp
        omega
      · simp
        omega

private theorem buildHeap_loop_time_le (k : Nat) (b : Array α) :
    (buildHeap.loop k b).time.2 ≤ ∑ i ∈ Finset.range k, heapHeight b.size i ∧
      (buildHeap.loop k b).time.1 ≤ 2 * ∑ i ∈ Finset.range k, heapHeight b.size i := by
  induction k generalizing b with
  | zero => simp [buildHeap.loop]
  | succ k ih =>
    have hs := siftDown_swaps_le_heapHeight b k
    have hc := siftDown_comparisons_le_heapHeight b k
    obtain ⟨hrs, hrc⟩ := ih (siftDown b k).ret
    rw [size_ret_siftDown] at hrs hrc
    simp only [buildHeap.loop, time_bind, Prod.fst_add, Prod.snd_add, Finset.sum_range_succ]
    omega

/-- **Bottom-up heap construction takes linear time.** Let $a$ be an array of length $n$ over a
linearly ordered type, let $b$ be the array returned by timed bottom-up heap construction on $a$,
and let $S = \sum_{i=0}^{n-1} \lfloor \log_2 \lfloor n/(i+1) \rfloor \rfloor$ be the sum of the
heights of the nodes of the level-order binary tree with $n$ nodes. Then:
1. $b$ is heap ordered and is a permutation of $a$;
2. the construction counts at most $S$ array swaps and at most $2S$ value comparisons;
3. $S = n - s_2(n)$, where $s_2(n)$ is the sum of the binary digits of $n$;
4. if $n = 2^{h+1} - 1$ for a natural number $h$, so that the tree is perfect of height $h$, then
   $S = 2^{h+1} - 1 - (h + 1)$. -/
theorem buildHeap_linear (a : Array α) :
    HeapOrdered (buildHeap a).ret ∧ (buildHeap a).ret.Perm a ∧
      (buildHeap a).time.2 ≤ ∑ i ∈ Finset.range a.size, heapHeight a.size i ∧
      (buildHeap a).time.1 ≤ 2 * ∑ i ∈ Finset.range a.size, heapHeight a.size i ∧
      ∑ i ∈ Finset.range a.size, heapHeight a.size i = a.size - (Nat.digits 2 a.size).sum ∧
      ∀ h : Nat, a.size = 2 ^ (h + 1) - 1 →
        ∑ i ∈ Finset.range a.size, heapHeight a.size i = 2 ^ (h + 1) - 1 - (h + 1) := by
  have hsub : ∑ i ∈ Finset.range (a.size / 2), heapHeight a.size i ≤
      ∑ i ∈ Finset.range a.size, heapHeight a.size i :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.div_le_self _ _))
  obtain ⟨hs, hc⟩ := buildHeap_loop_time_le (a.size / 2) a
  have hsum := sum_heapHeight_add_digits_sum a.size
  refine ⟨by simpa using buildHeap_ordered a, by simpa using buildHeap_perm a,
    hs.trans hsub, hc.trans (Nat.mul_le_mul_left 2 hsub), by omega, ?_⟩
  intro h hsize
  have hdigits := digits_sum_two_pow_sub_one (h + 1)
  have hperfect := sum_heapHeight_add_digits_sum (2 ^ (h + 1) - 1)
  rw [hsize]
  omega

end TimeM

end Cslib.Algorithms.Lean
