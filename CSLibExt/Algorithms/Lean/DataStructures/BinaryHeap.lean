/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Multiset.AddSub

/-!
# Binary min-heaps

This file defines a binary min-heap backed by a level-order array. Sifting swaps entries only
along one ancestor or descendant path. The public theorems prove local heap order, global root
minimality, permutation laws, and exact multiplicity behavior for insertion and extraction.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

set_option autoImplicit false

universe u

/-- **Parent index in a level-order binary tree.** In a binary tree stored in level order in an
array indexed from $0$, the parent index of a natural number $i$ is $\lfloor (i-1)/2 \rfloor$,
where $i - 1$ is truncated subtraction of natural numbers, so the root index $0$ is sent to $0$. -/
def heapParent (i : Nat) : Nat := (i - 1) / 2

/-- **Left child index in a level-order binary tree.** In a binary tree stored in level order in
an array indexed from $0$, the left child of the node at index $i$ has index $2i + 1$. -/
def heapLeft (i : Nat) : Nat := 2 * i + 1

/-- **Right child index in an array-backed binary tree.** In the level-order layout of a binary
tree in an array indexed from $0$, the right child of the node at index $i$ is at index $2i + 2$. -/
def heapRight (i : Nat) : Nat := 2 * i + 2

private theorem heapParent_lt (i : Nat) (hi : 0 < i) : heapParent i < i := by
  unfold heapParent
  have hdiv : (i - 1) / 2 ≤ i - 1 := Nat.div_le_self _ _
  omega

/-- **The parent of a valid nonroot index is valid.** For an array $a$ of length $|a|$ and an index
$i$ with $0 < i < |a|$, the parent index $\lfloor (i-1)/2 \rfloor$ of $i$ is also less than
$|a|$. -/
theorem heapParent_lt_size {α : Type u} (a : Array α) (i : Nat)
    (hi : i < a.size) (hpos : 0 < i) : heapParent i < a.size := by
  exact (heapParent_lt i hpos).trans hi

/-- **Heap order on a level-order array.** An array $a$ over a type with a relation $\le$, indexed
from $0$, is heap ordered when every entry other than the root is at least its parent entry:
for every index $i$ with $0 < i < |a|$, where $|a|$ is the length of $a$, we have
$a_{\lfloor (i-1)/2 \rfloor} \le a_i$. -/
def HeapOrdered {α : Type u} [LE α] (a : Array α) : Prop :=
  ∀ i (hi : i < a.size), (hpos : 0 < i) →
    a[heapParent i]'(heapParent_lt_size a i hi hpos) ≤ a[i]

/-- **Arrays ready for sift-up.** Let $a$ be an array of length $|a|$ over a type with a relation
$\le$, indexed from $0$, and for $j > 0$ let $p(j) = \lfloor (j - 1)/2 \rfloor$ be the parent of
$j$. The array $a$ is ready for sift-up at an index $i$ when $i < |a|$, when $a_{p(j)} \le a_j$ for
every $j \ne i$ with $0 < j < |a|$, and when, if $i > 0$, also $a_{p(i)} \le a_j$ for every $j$
with $0 < j < |a|$ and $p(j) = i$. -/
structure SiftUpReady {α : Type u} [LE α] (a : Array α) (i : Nat) : Prop where
  index_valid : i < a.size
  ordered_except : ∀ j (hj : j < a.size), (hjpos : 0 < j) → j ≠ i →
    a[heapParent j]'(heapParent_lt_size a j hj hjpos) ≤ a[j]
  parent_below_children : ∀ j (hj : j < a.size), (hjpos : 0 < j) →
    heapParent j = i → (hipos : 0 < i) →
    a[heapParent i]'(heapParent_lt_size a i index_valid hipos) ≤ a[j]

/-- **Sift-down precondition.** For an array $a$ over a type ordered by $\le$, write
$p(j) = \lfloor (j-1)/2 \rfloor$ for the parent of index $j$. The array $a$ is ready for
sift-down at index $i$ when $i$ is a valid index of $a$; $a_{p(j)} \le a_j$ for every valid index
$j > 0$ with $p(j) \ne i$; and, if $i > 0$, $a_{p(i)} \le a_j$ for every valid index $j > 0$ with
$p(j) = i$.

Thus the only edges that may violate heap order are those leaving $i$, and moving either child
of $i$ up to position $i$ keeps the edge entering $i$ ordered. -/
structure SiftDownReady {α : Type u} [LE α] (a : Array α) (i : Nat) : Prop where
  index_valid : i < a.size
  ordered_except : ∀ j (hj : j < a.size), (hjpos : 0 < j) →
    heapParent j ≠ i →
    a[heapParent j]'(heapParent_lt_size a j hj hjpos) ≤ a[j]
  parent_below_children : ∀ j (hj : j < a.size), (hjpos : 0 < j) →
    heapParent j = i → (hipos : 0 < i) →
    a[heapParent i]'(heapParent_lt_size a i index_valid hipos) ≤ a[j]

@[simp] private theorem heapParent_left (i : Nat) :
    heapParent (heapLeft i) = i := by
  simp only [heapParent, heapLeft]
  apply Nat.div_eq_of_lt_le <;> omega

@[simp] private theorem heapParent_right (i : Nat) :
    heapParent (heapRight i) = i := by
  simp only [heapParent, heapRight]
  apply Nat.div_eq_of_lt_le <;> omega

private theorem eq_left_or_right (i j : Nat) (hjpos : 0 < j)
    (hp : heapParent j = i) : j = heapLeft i ∨ j = heapRight i := by
  have lo : i * 2 ≤ j - 1 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp
    change (j - 1) / 2 = i at hp
    rw [hp]
  have hi : j - 1 < (i + 1) * 2 := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mp
    change (j - 1) / 2 = i at hp
    rw [hp]
    omega
  simp only [heapLeft, heapRight]
  omega

/-- **Smaller child.** Let $a$ be an array of length $|a|$ over a linearly ordered type, indexed
from $0$, and let $i$ be an index with children $\ell = 2i + 1$ and $r = 2i + 2$. If
$\ell \ge |a|$, then $i$ has no smaller child. Otherwise the smaller child of $i$ is $r$ when
$r < |a|$ and $a_r < a_\ell$, and $\ell$ in every other case, so ties go to the left child. -/
def smallerChild {α : Type u} [LinearOrder α]
    (a : Array α) (i : Nat) : Option Nat :=
  if hl : heapLeft i < a.size then
    if hr : heapRight i < a.size then
      if a[heapRight i] < a[heapLeft i] then
        some (heapRight i)
      else
        some (heapLeft i)
    else
      some (heapLeft i)
  else
    none

private theorem smallerChild_parent {α : Type u} [LinearOrder α]
    (a : Array α) (i c : Nat)
    (h : smallerChild a i = some c) : heapParent c = i := by
  unfold smallerChild at h
  split at h
  · split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst c
        exact heapParent_right i
      · simp only [Option.some.injEq] at h
        subst c
        exact heapParent_left i
    · simp only [Option.some.injEq] at h
      subst c
      exact heapParent_left i
  · contradiction

/-- **The smaller child has a larger index.** For every array $a$ over a linearly ordered type
and all indices $i$ and $c$, if $c$ is the smaller child of $i$ in $a$, then $i < c$. -/
theorem smallerChild_gt {α : Type u} [LinearOrder α]
    (a : Array α) (i c : Nat)
    (h : smallerChild a i = some c) : i < c := by
  unfold smallerChild at h
  split at h
  · split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst c
        unfold heapRight
        omega
      · simp only [Option.some.injEq] at h
        subst c
        unfold heapLeft
        omega
    · simp only [Option.some.injEq] at h
      subst c
      unfold heapLeft
      omega
  · contradiction

/-- **The smaller child is a valid index.** For every array $a$ over a linearly ordered type and
all indices $i$ and $c$, if $c$ is the smaller child of $i$ in $a$, then $c$ is less than the
length $|a|$ of $a$. -/
theorem smallerChild_valid {α : Type u} [LinearOrder α]
    (a : Array α) (i c : Nat)
    (h : smallerChild a i = some c) : c < a.size := by
  unfold smallerChild at h
  split at h
  · split at h
    · split at h <;> simp only [Option.some.injEq] at h <;> subst c <;>
        assumption
    · simp only [Option.some.injEq] at h
      subst c
      assumption
  · contradiction

private theorem smallerChild_le {α : Type u} [LinearOrder α]
    (a : Array α) (i c : Nat)
    (h : smallerChild a i = some c) (j : Nat) (hj : j < a.size)
    (hjpos : 0 < j) (hp : heapParent j = i) :
    a[c]'(smallerChild_valid a i c h) ≤ a[j] := by
  unfold smallerChild at h
  split at h
  · split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst c
        rcases eq_left_or_right i j hjpos hp with rfl | rfl
        · exact le_of_lt ‹a[heapRight i] < a[heapLeft i]›
        · exact le_rfl
      · simp only [Option.some.injEq] at h
        subst c
        rcases eq_left_or_right i j hjpos hp with rfl | rfl
        · exact le_rfl
        · exact le_of_not_gt ‹¬a[heapRight i] < a[heapLeft i]›
    · simp only [Option.some.injEq] at h
      subst c
      rcases eq_left_or_right i j hjpos hp with rfl | rfl
      · exact le_rfl
      · omega
  · contradiction

/-- **Sift-up.** Given an array $a$ of length $|a|$ over a linearly ordered type, indexed from $0$,
and an index $i$, the sift-up of $a$ from $i$ is defined by recursion on $i$. If $i = 0$ or
$i \ge |a|$, the result is $a$. Otherwise let $p = \lfloor (i - 1)/2 \rfloor$ be the parent of
$i$; if $a_i < a_p$, the result is the sift-up from $p$ of the array obtained from $a$ by
exchanging the entries at positions $i$ and $p$, and otherwise the result is $a$. -/
def siftUp {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) : Array α :=
  if hi : i < a.size then
    if hpos : 0 < i then
      let p := heapParent i
      if hlt : a[i] < a[p]'(heapParent_lt_size a i hi hpos) then
        siftUp (a.swap i p hi (heapParent_lt_size a i hi hpos)) p
      else
        a
    else
      a
  else
    a
termination_by i
decreasing_by
  exact heapParent_lt i hpos

/-- **Sift-down.** Sifting down an array $a$ over a linearly ordered type from index $i$ works as
follows. If $i$ has a child in $a$, that is, if $2i+1$ is a valid index, let $c$ be the child of
$i$ (among $2i+1$ and $2i+2$, if valid) holding the smaller value, preferring the left child
$2i+1$ on ties. If $a_c < a_i$, swap the entries at $i$ and $c$ and continue sifting down from
$c$; otherwise, or if $i$ has no child, return the array unchanged. -/
def siftDown {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) : Array α :=
  match hchild : smallerChild a i with
  | none => a
  | some c =>
    have hc : c < a.size := smallerChild_valid a i c hchild
    have hi : i < a.size := (smallerChild_gt a i c hchild).trans hc
    if hlt : a[c] < a[i] then
      siftDown (a.swap i c hi hc) c
    else
      a
termination_by a.size - i
decreasing_by
  simp only [Array.size_swap]
  have := smallerChild_gt a i c hchild
  omega

/-- **Sift-up permutes the array.** For every array $a$ over a linearly ordered type and every
index $i$, the array obtained by sifting up $a$ from $i$ is a permutation of $a$. -/
theorem siftUp_perm {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    (siftUp a i).Perm a := by
  induction i using Nat.strong_induction_on generalizing a with
  | h i ih =>
    rw [siftUp]
    split
    · split
      · dsimp only
        split
        · exact (ih (heapParent i) (heapParent_lt i ‹0 < i›) _).trans
            (Array.swap_perm _ _)
        · exact Array.Perm.refl _
      · exact Array.Perm.refl _
    · exact Array.Perm.refl _

/-- **Binary-heap sift-down permutes the array.** For every array $a$ over a linearly ordered
type and every index $i$, the array obtained by sifting down $a$ from $i$ is a permutation of
$a$. -/
theorem siftDown_perm {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    (siftDown a i).Perm a := by
  induction hm : a.size - i using Nat.strong_induction_on generalizing a i with
  | h n ih =>
    rw [siftDown]
    split
    · exact Array.Perm.refl _
    · rename_i c hchild
      dsimp only
      split
      · have hc := smallerChild_valid a i c hchild
        have hi := (smallerChild_gt a i c hchild).trans hc
        have hdec : (a.swap i c hi hc).size - c < n := by
            simp only [Array.size_swap]
            rw [← hm]
            have := smallerChild_gt a i c hchild
            omega
        exact (ih _ hdec (a.swap i c hi hc) c rfl).trans
          (Array.swap_perm hi hc)
      · exact Array.Perm.refl _

/-- **Binary-heap sift-up preserves the multiset of entries.** For every array $a$ over a
linearly ordered type and every index $i$, the array obtained by sifting up $a$ from $i$ has the
same multiset of entries as $a$. -/
theorem siftUp_multiset {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    (↑(siftUp a i).toList : Multiset α) = (↑a.toList : Multiset α) :=
  Multiset.coe_eq_coe.mpr (siftUp_perm a i).toList

/-- **Binary-heap sift-down preserves the multiset of entries.** For every array $a$ over a
linearly ordered type and every index $i$, the array obtained by sifting down $a$ from $i$ has
the same multiset of entries as $a$. -/
theorem siftDown_multiset {α : Type u} [LinearOrder α] (a : Array α) (i : Nat) :
    (↑(siftDown a i).toList : Multiset α) = (↑a.toList : Multiset α) :=
  Multiset.coe_eq_coe.mpr (siftDown_perm a i).toList

/-- **The root of a heap-ordered binary-heap array is minimal.** If an array $a$ over a linearly
ordered type is heap-ordered, then $a_0 \le a_i$ for every valid index $i$ of $a$. -/
theorem HeapOrdered.root_le {α : Type u} [LinearOrder α] {a : Array α}
    (h : HeapOrdered a) (i : Nat) (hi : i < a.size) :
    a[0]'(by omega) ≤ a[i] := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hzero : i = 0
    · subst i
      exact le_rfl
    · have hpos : 0 < i := by omega
      exact (ih (heapParent i) (heapParent_lt i hpos)
        (heapParent_lt_size a i hi hpos)).trans (h i hi hpos)

private theorem siftUpReady_swap {α : Type u} [LinearOrder α]
    (a : Array α) (i : Nat) (h : SiftUpReady a i) (hpos : 0 < i)
    (hlt : a[i]'h.index_valid <
      a[heapParent i]'(heapParent_lt_size a i h.index_valid hpos)) :
    SiftUpReady
      (a.swap i (heapParent i) h.index_valid
        (heapParent_lt_size a i h.index_valid hpos))
      (heapParent i) := by
  let p := heapParent i
  have hp : p < a.size := heapParent_lt_size a i h.index_valid hpos
  have hpi : p < i := heapParent_lt i hpos
  refine {
    index_valid := ?_
    ordered_except := ?_
    parent_below_children := ?_
  }
  · simpa [p] using hp
  · intro j hj hjpos hjne
    have hja : j < a.size := by simpa [p] using hj
    have hjp : j ≠ p := by simpa [p] using hjne
    by_cases hji : j = i
    · subst j
      simp [hlt.le]
    · by_cases hparenti : heapParent j = i
      · have hold := h.parent_below_children j hja hjpos hparenti hpos
        simpa only [Array.getElem_swap, hparenti, hji, hjp, p, ite_true, ite_false]
          using hold
      · by_cases hparentp : heapParent j = p
        · have hold := h.ordered_except j hja hjpos hji
          have hold' : a[p]'hp ≤ a[j] := by
            simpa only [hparentp] using hold
          have hchain := hlt.le.trans hold'
          simpa only [Array.getElem_swap, hparenti, hparentp, hji, hjp, hpi.ne, p,
            ite_true, ite_false] using hchain
        · have hold := h.ordered_except j hja hjpos hji
          rw [Array.getElem_swap_of_ne hparenti hparentp,
            Array.getElem_swap_of_ne hji hjp]
          exact hold
  · intro j hj hjpos hparent hppos
    have hja : j < a.size := by simpa [p] using hj
    have hparent' : heapParent j = p := by simpa [p] using hparent
    have hppos' : 0 < p := by simpa [p] using hppos
    have hp_parent_lt := heapParent_lt p hppos'
    have hppi : heapParent p ≠ i := by omega
    by_cases hji : j = i
    · subst j
      have hold := h.ordered_except p hp hppos' (by omega)
      rw [Array.getElem_swap_of_ne hppi hp_parent_lt.ne,
        Array.getElem_swap_left]
      simpa only [p] using hold
    · have hjp : j ≠ p := by
        intro heq
        subst j
        exact (heapParent_lt p hppos').ne hparent'
      have hold := h.ordered_except j hja hjpos (by omega)
      have hold' : a[p]'hp ≤ a[j] := by
        simpa only [hparent'] using hold
      have hparentEdge := h.ordered_except p hp hppos' (by omega)
      have hchain := hparentEdge.trans hold'
      rw [Array.getElem_swap_of_ne hppi hp_parent_lt.ne,
        Array.getElem_swap_of_ne hji hjp]
      simpa only [p] using hchain

private theorem SiftUpReady.ordered_of_not_lt {α : Type u} [LinearOrder α]
    {a : Array α} {i : Nat} (h : SiftUpReady a i) (hpos : 0 < i)
    (hnlt : ¬a[i]'h.index_valid <
      a[heapParent i]'(heapParent_lt_size a i h.index_valid hpos)) :
    HeapOrdered a := by
  intro j hj hjpos
  if hji : j = i then
    subst j
    exact le_of_not_gt hnlt
  else
    exact h.ordered_except j hj hjpos hji

private theorem SiftUpReady.ordered_at_root {α : Type u} [LinearOrder α]
    {a : Array α} (h : SiftUpReady a 0) : HeapOrdered a := by
  intro j hj hjpos
  exact h.ordered_except j hj hjpos (Nat.ne_of_gt hjpos)

/-- **Sift-up restores heap order.** Let $a$ be an array over a linearly ordered type and let
$i$ be an index such that $a$ is ready for sift-up at $i$. Then the array obtained by sifting
up $a$ from $i$ is heap ordered. -/
theorem siftUp_ordered {α : Type u} [LinearOrder α] (a : Array α) (i : Nat)
    (h : SiftUpReady a i) : HeapOrdered (siftUp a i) := by
  induction i using Nat.strong_induction_on generalizing a with
  | h i ih =>
    rw [siftUp]
    split
    · split
      · dsimp only
        split
        · have hlt' : a[i]'h.index_valid <
            a[heapParent i]'(heapParent_lt_size a i h.index_valid ‹0 < i›) := by
            assumption
          apply ih (heapParent i) (heapParent_lt i ‹0 < i›)
          exact siftUpReady_swap a i h ‹0 < i› hlt'
        · intro j hj hjpos
          exact h.ordered_of_not_lt ‹0 < i› (by assumption) j hj hjpos
      · have hi0 : i = 0 := by omega
        subst i
        exact h.ordered_at_root
    · exact False.elim (‹¬i < a.size› h.index_valid)

private theorem siftDownReady_swap {α : Type u} [LinearOrder α]
    (a : Array α) (i c : Nat) (hchild : smallerChild a i = some c)
    (h : SiftDownReady a i)
    (hlt : a[c]'(smallerChild_valid a i c hchild) < a[i]'h.index_valid) :
    SiftDownReady
      (a.swap i c h.index_valid (smallerChild_valid a i c hchild)) c := by
  have hc : c < a.size := smallerChild_valid a i c hchild
  have hic : i < c := smallerChild_gt a i c hchild
  have hpci : heapParent c = i := smallerChild_parent a i c hchild
  refine {
    index_valid := by simpa using hc
    ordered_except := ?_
    parent_below_children := ?_
  }
  · intro j hj hjpos hparentc
    have hja : j < a.size := by simpa using hj
    by_cases hjc : j = c
    · subst j
      simp [hpci, hlt.le]
    · by_cases hji : j = i
      · subst j
        have hipos : 0 < i := hjpos
        have hold := h.parent_below_children c hc (by omega) hpci hipos
        have hparent_ne_c : heapParent i ≠ c := by
          have := heapParent_lt i hipos
          omega
        have hparent_ne_i : heapParent i ≠ i := (heapParent_lt i hipos).ne
        rw [Array.getElem_swap_of_ne hparent_ne_i hparent_ne_c,
          Array.getElem_swap_left]
        exact hold
      · by_cases hparenti : heapParent j = i
        · have hold := smallerChild_le a i c hchild j hja hjpos hparenti
          simpa only [Array.getElem_swap, hparenti, hji, hjc, hic.ne, ite_true,
            ite_false] using hold
        · have hold := h.ordered_except j hja hjpos hparenti
          have hparent_ne_c : heapParent j ≠ c := hparentc
          rw [Array.getElem_swap_of_ne hparenti hparent_ne_c,
            Array.getElem_swap_of_ne hji hjc]
          exact hold
  · intro j hj hjpos hparent hcp
    have hja : j < a.size := by simpa using hj
    have hparent' : heapParent j = c := by simpa using hparent
    have hjc : j ≠ c := by
      intro heq
      subst j
      exact (heapParent_lt c hcp).ne hparent'
    have hcj : c < j := by
      rw [← hparent']
      exact heapParent_lt j hjpos
    have hji : j ≠ i := by omega
    have hold := h.ordered_except j hja hjpos (by omega)
    have hold' : a[c]'hc ≤ a[j] := by simpa only [hparent'] using hold
    simpa only [Array.getElem_swap, hpci, hji, hjc, hic.ne, ite_true, ite_false]
      using hold'

private theorem no_smallerChild_ordered {α : Type u} [LinearOrder α]
    (a : Array α) (i : Nat) (h : SiftDownReady a i)
    (hnone : smallerChild a i = none) : HeapOrdered a := by
  have hlbad : ¬heapLeft i < a.size := by
    intro hl
    unfold smallerChild at hnone
    simp only [hl] at hnone
    by_cases hr : heapRight i < a.size
    · simp only [hr] at hnone
      by_cases hcmp : a[heapRight i] < a[heapLeft i]
      · simp only [hcmp] at hnone
        contradiction
      · simp only [hcmp] at hnone
        contradiction
    · simp only [hr] at hnone
      contradiction
  intro j hj hjpos
  by_cases hp : heapParent j = i
  · rcases eq_left_or_right i j hjpos hp with rfl | rfl
    · exact (hlbad hj).elim
    · have hr : heapRight i < a.size := hj
      have hl : heapLeft i < a.size := by
        simp [heapLeft, heapRight] at hr ⊢
        omega
      exact (hlbad hl).elim
  · exact h.ordered_except j hj hjpos hp

private theorem no_swap_ordered {α : Type u} [LinearOrder α]
    (a : Array α) (i c : Nat) (h : SiftDownReady a i)
    (hchild : smallerChild a i = some c)
    (hnlt : ¬a[c]'(smallerChild_valid a i c hchild) < a[i]'h.index_valid) :
    HeapOrdered a := by
  intro j hj hjpos
  by_cases hp : heapParent j = i
  · have hbase :=
      (le_of_not_gt hnlt).trans (smallerChild_le a i c hchild j hj hjpos hp)
    simpa only [hp] using hbase
  · exact h.ordered_except j hj hjpos hp

/-- **Sift-down restores heap order.** Let $a$ be an array over a linearly ordered type that
satisfies the sift-down precondition at a valid index $i$: the only edges that may violate heap
order are those leaving $i$, and moving either child of $i$ up to position $i$ keeps the edge
entering $i$ ordered. Then the array obtained by sifting down $a$ from $i$ is heap-ordered. -/
theorem siftDown_ordered {α : Type u} [LinearOrder α] (a : Array α) (i : Nat)
    (h : SiftDownReady a i) : HeapOrdered (siftDown a i) := by
  induction hm : a.size - i using Nat.strong_induction_on generalizing a i with
  | h n ih =>
    rw [siftDown]
    split
    · rename_i hchild
      exact no_smallerChild_ordered a i h hchild
    · rename_i c hchild
      dsimp only
      split
      · have hlt' : a[c]'(smallerChild_valid a i c hchild) < a[i]'h.index_valid := by
          assumption
        have hready := siftDownReady_swap a i c hchild h hlt'
        have hdec : (a.swap i c h.index_valid
            (smallerChild_valid a i c hchild)).size - c < n := by
          simp only [Array.size_swap]
          rw [← hm]
          have := smallerChild_gt a i c hchild
          have := smallerChild_valid a i c hchild
          have := h.index_valid
          omega
        exact ih _ hdec _ _ hready rfl
      · have hnlt' :
            ¬a[c]'(smallerChild_valid a i c hchild) < a[i]'h.index_valid := by
          assumption
        exact no_swap_ordered a i c h hchild hnlt'

/-- **Appending to a heap-ordered array prepares it for sift-up.** If an array $a$ of length $n$
over a linearly ordered type is heap-ordered and $x$ is any value, then the array obtained by
appending $x$ to $a$ satisfies the sift-up precondition at index $n$, the position of $x$: the
only edge that may violate heap order is the one entering index $n$. -/
theorem push_siftUpReady {α : Type u} [LinearOrder α] (a : Array α)
    (h : HeapOrdered a) (x : α) : SiftUpReady (a.push x) a.size := by
  refine {
    index_valid := by
      simpa only [Array.size_push] using Nat.lt_succ_self a.size
    ordered_except := ?_
    parent_below_children := ?_
  }
  · intro j hj hjpos hjne
    have hjlt : j < a.size := by
      simp only [Array.size_push] at hj
      omega
    have hplt : heapParent j < a.size := heapParent_lt_size a j hjlt hjpos
    simpa only [Array.getElem_push_lt hjlt, Array.getElem_push_lt hplt] using
      h j hjlt hjpos
  · intro j hj hjpos hp _
    have hp_lt_j := heapParent_lt j hjpos
    simp only [Array.size_push] at hj
    omega

/-- **Binary min-heap.** A binary min-heap over a linearly ordered type $\alpha$ is an array $a$
of elements of $\alpha$ (its level-order storage), of length $|a|$ and with entries
$a_0, \dots, a_{|a|-1}$, that is heap ordered: for every index $i$ with $0 < i < |a|$, the entry
$a_{\lfloor (i - 1)/2 \rfloor}$ at the parent index of $i$ is at most $a_i$. -/
structure MinHeap (α : Type u) [LinearOrder α] where
  /-- The level-order storage array. -/
  data : Array α
  ordered : HeapOrdered data

/-- **Elements of a binary min-heap.** The multiset of elements of a binary min-heap is the
multiset of the entries of its level-order storage array, counted with multiplicity. -/
def MinHeap.elements {α : Type u} [LinearOrder α] (h : MinHeap α) : Multiset α :=
  h.data.toList

/-- **Empty binary min-heap.** The empty binary min-heap is the min-heap whose level-order storage
array has no entries. -/
def MinHeap.empty {α : Type u} [LinearOrder α] : MinHeap α where
  data := #[]
  ordered := by simp [HeapOrdered]

/-- **Insertion into a binary min-heap.** To insert a value $x$ into a binary min-heap $h$, append
$x$ at the end of the level-order array of $h$ and sift it up from its index (the old length of
the array), repeatedly swapping it with its parent while it is smaller. The result is again a
binary min-heap. -/
def MinHeap.push {α : Type u} [LinearOrder α] (h : MinHeap α) (x : α) : MinHeap α where
  data := siftUp (h.data.push x) h.data.size
  ordered := siftUp_ordered _ _ (push_siftUpReady h.data h.ordered x)

/-- **Minimum lookup in a binary heap.** For a binary min-heap $h$, the minimum lookup returns the
entry at index $0$ (the root) of the storage array of $h$ when that array is nonempty, and returns
no value when it is empty. -/
def MinHeap.min? {α : Type u} [LinearOrder α] (h : MinHeap α) : Option α :=
  h.data[0]?

/-- **Binary heap minimum lookup fails exactly when empty.** For a binary min-heap $h$ over a
linearly ordered type, looking up the minimum of $h$ returns no value if and only if the storage
array of $h$ has size $0$. -/
theorem MinHeap.min?_eq_none_iff {α : Type u} [LinearOrder α] (h : MinHeap α) :
    h.min? = none ↔ h.data.size = 0 := by
  simp [MinHeap.min?, getElem?_def]

/-- **Binary heap minimum lookup succeeds exactly when nonempty.** For a binary min-heap $h$ over
a linearly ordered type, looking up the minimum of $h$ returns a value if and only if the storage
array of $h$ has positive size. -/
theorem MinHeap.min?_isSome_iff {α : Type u} [LinearOrder α] (h : MinHeap α) :
    h.min?.isSome ↔ 0 < h.data.size := by
  simp [MinHeap.min?, getElem?_def]

/-- **The binary heap minimum lookup returns a stored element.** Let $h$ be a binary min-heap
over a linearly ordered type. If looking up the minimum of $h$ returns $x$, then $x$ belongs to
the multiset of elements of $h$. -/
theorem MinHeap.min?_mem {α : Type u} [LinearOrder α] {h : MinHeap α} {x : α}
    (hx : h.min? = some x) : x ∈ h.elements := by
  unfold MinHeap.min? at hx
  simp only [getElem?_def] at hx
  split at hx
  · simp only [Option.some.injEq] at hx
    subst x
    simp [MinHeap.elements, Array.mem_toList_iff]
  · contradiction

/-- **The binary heap minimum lookup is a lower bound.** Let $h$ be a binary min-heap over a
linearly ordered type. If looking up the minimum of $h$ returns $x$, then $x \le y$ for every
element $y$ of the multiset of elements of $h$. -/
theorem MinHeap.min?_le {α : Type u} [LinearOrder α] {h : MinHeap α} {x y : α}
    (hx : h.min? = some x) (hy : y ∈ h.elements) : x ≤ y := by
  unfold MinHeap.min? at hx
  simp only [getElem?_def] at hx
  split at hx
  · simp only [Option.some.injEq] at hx
    subst x
    change y ∈ h.data.toList at hy
    rcases List.mem_iff_getElem.mp hy with ⟨i, hi, rfl⟩
    simpa using h.ordered.root_le i (by simpa using hi)
  · contradiction

/-- **Elements after binary heap insertion.** Let $h$ be a binary min-heap over a linearly ordered
type and $x$ a value. The multiset of elements of the heap obtained by inserting $x$ into $h$ is
the multiset of elements of $h$ with one more copy of $x$ added. -/
theorem MinHeap.elements_push {α : Type u} [LinearOrder α] (h : MinHeap α) (x : α) :
    (h.push x).elements = x ::ₘ h.elements := by
  have hp := (siftUp_perm (h.data.push x) h.data.size).toList
  rw [Array.toList_push] at hp
  apply Multiset.coe_eq_coe.mpr
  exact hp.trans List.perm_append_comm

/-- **Binary heap insertion adds one copy of the inserted value.** Let $h$ be a binary min-heap
over a linearly ordered type and $x$ a value. The multiplicity of $x$ in the multiset of elements
of the heap obtained by inserting $x$ into $h$ is one more than its multiplicity in the multiset
of elements of $h$. -/
theorem MinHeap.count_push_self {α : Type u} [LinearOrder α]
    (h : MinHeap α) (x : α) :
    Multiset.count x (h.push x).elements = Multiset.count x h.elements + 1 := by
  rw [h.elements_push x]
  simp

/-- **Binary heap insertion leaves other multiplicities unchanged.** Let $h$ be a binary min-heap
over a linearly ordered type, and let $x \ne y$ be values. Then $y$ occurs in the multiset of
elements of the heap obtained by inserting $x$ into $h$ exactly as many times as it occurs in the
multiset of elements of $h$. -/
theorem MinHeap.count_push_of_ne {α : Type u} [LinearOrder α]
    (h : MinHeap α) {x y : α} (hyx : y ≠ x) :
    Multiset.count y (h.push x).elements = Multiset.count y h.elements := by
  rw [h.elements_push x]
  simp [hyx]

/-- **Insertion into a binary min-heap preserves heap order.** For every binary min-heap $h$
over a linearly ordered type and every value $x$, the level-order array of the heap obtained
by inserting $x$ into $h$ is heap-ordered: the entry at every nonroot index $i$ is at least
the entry at its parent index $\lfloor (i-1)/2 \rfloor$. -/
theorem MinHeap.push_ordered {α : Type u} [LinearOrder α] (h : MinHeap α) (x : α) :
    HeapOrdered (h.push x).data :=
  (h.push x).ordered

/-- **Moving the last entry to the root.** For a nonempty array $a$ of length $n$, this operation
swaps the entries at indices $0$ and $n - 1$ and then deletes the final entry. The result has
length $n - 1$; when $n \ge 2$ its entry at index $0$ is $a_{n-1}$ and its entry at each index
$0 < i < n - 1$ is $a_i$. -/
def moveLastToRoot {α : Type u} (a : Array α) (hne : 0 < a.size) : Array α :=
  (a.swap 0 (a.size - 1) hne (by omega)).pop

/-- **Moving the last entry to the root prepares a sift-down.** Let $a$ be a heap-ordered array
over a linearly ordered type with at least two entries, and let $b$ be the array obtained from $a$
by moving its last entry to the root. Then $b$ is ready for sifting down at index $0$: index $0$ is
valid in $b$, and for every index $j > 0$ of $b$ whose parent index $\lfloor (j - 1)/2 \rfloor$ is
not $0$, the entry of $b$ at the parent index is at most $b_j$. -/
theorem moveLastToRoot_siftDownReady {α : Type u} [LinearOrder α]
    (a : Array α) (h : HeapOrdered a) (htwo : 1 < a.size) :
    SiftDownReady (moveLastToRoot a (by omega)) 0 := by
  let last := a.size - 1
  have hzero : 0 < a.size := by omega
  have hlast : last < a.size := by omega
  refine {
    index_valid := by simp [moveLastToRoot]; omega
    ordered_except := ?_
    parent_below_children := ?_
  }
  · intro j hj hjpos hpzero
    have hjlt : j < a.size - 1 := by
      simpa [moveLastToRoot] using hj
    have hja : j < a.size := by omega
    have hjlast : j ≠ last := by omega
    have hparent_lt := heapParent_lt j hjpos
    have hparentlast : heapParent j ≠ last := by omega
    have hold := h j hja hjpos
    simpa only [moveLastToRoot, Array.getElem_pop, Array.getElem_swap, last,
      hpzero, hjlast, hparentlast, ne_of_gt hjpos, ite_false] using hold
  · intro _ _ _ _ hzero'
    omega

private theorem moveLastToRoot_cons_perm {α : Type u} [LinearOrder α]
    (a : Array α) (hne : 0 < a.size) :
    (a[0]'hne :: (moveLastToRoot a hne).toList).Perm a.toList := by
  let last := a.size - 1
  let b := a.swap 0 last hne (by omega)
  have hbne : b.toList ≠ [] := by
    intro heq
    have hbpos : 0 < b.toList.length := by simpa [b] using hne
    rw [heq] at hbpos
    simp at hbpos
  have hlast : b.toList.getLast hbne = a[0]'hne := by
    rw [List.getLast_eq_getElem]
    simp [b, last]
  have hdecomp := List.dropLast_append_getLast hbne
  rw [hlast] at hdecomp
  have hperm : (a[0]'hne :: b.toList.dropLast).Perm b.toList := by
    exact List.perm_append_comm.trans (List.Perm.of_eq hdecomp)
  have hswap := (Array.swap_perm hne (by omega : a.size - 1 < a.size)).toList
  simpa [moveLastToRoot, b, Array.toList_pop] using hperm.trans hswap

/-- **Moving the last entry to the root removes the old root.** For a nonempty array $a$ over a
linearly ordered type, the multiset of entries of the array obtained from $a$ by moving its last
entry to the root equals the multiset of entries of $a$ with one occurrence of $a_0$ removed. -/
theorem moveLastToRoot_elements {α : Type u} [LinearOrder α]
    (a : Array α) (hne : 0 < a.size) :
    (↑(moveLastToRoot a hne).toList : Multiset α) =
      (↑a.toList : Multiset α).erase (a[0]'hne) := by
  have hp := moveLastToRoot_cons_perm a hne
  have hm : a[0]'hne ::ₘ (↑(moveLastToRoot a hne).toList : Multiset α) =
      (↑a.toList : Multiset α) := Multiset.coe_eq_coe.mpr hp
  rw [← hm, Multiset.erase_cons_head]

/-- **Removing the root of a nonempty binary min-heap.** Let $h$ be a binary min-heap over a
linearly ordered type whose level-order array is nonempty. If the array has exactly one entry,
the result is the empty heap. Otherwise the last entry of the array replaces the root, the array
shrinks by one, and the result is the heap obtained by sifting this entry down from the root. -/
def MinHeap.extractTail {α : Type u} [LinearOrder α]
    (h : MinHeap α) (hne : 0 < h.data.size) : MinHeap α :=
  if hone : h.data.size = 1 then
    MinHeap.empty
  else
    have htwo : 1 < h.data.size := by omega
    let moved := moveLastToRoot h.data hne
    ⟨siftDown moved 0,
      siftDown_ordered moved 0
        (moveLastToRoot_siftDownReady h.data h.ordered htwo)⟩

private theorem MinHeap.extractTail_elements {α : Type u} [LinearOrder α]
    (h : MinHeap α) (hne : 0 < h.data.size) :
    (h.extractTail hne).elements = h.elements.erase (h.data[0]'hne) := by
  unfold MinHeap.extractTail
  split
  · have hlist : h.data.toList = [h.data[0]'hne] := by
      apply List.ext_get
      · simp
        omega
      · intro i hi₁ hi₂
        have hi : i = 0 := by
          simp at hi₂
          omega
        subst i
        simp [Array.getElem_toList]
    change ((#[] : Array α).toList : Multiset α) =
      (↑h.data.toList : Multiset α).erase (h.data[0]'hne)
    rw [hlist]
    simp
  · have hp := (siftDown_perm (moveLastToRoot h.data hne) 0).toList
    have hm :
        (↑(siftDown (moveLastToRoot h.data hne) 0).toList : Multiset α) =
        (↑(moveLastToRoot h.data hne).toList : Multiset α) :=
      Multiset.coe_eq_coe.mpr hp
    change (↑(siftDown (moveLastToRoot h.data hne) 0).toList : Multiset α) =
      (↑h.data.toList : Multiset α).erase (h.data[0]'hne)
    exact hm.trans (moveLastToRoot_elements h.data hne)

private theorem MinHeap.extractTail_cons_elements {α : Type u} [LinearOrder α]
    (h : MinHeap α) (hne : 0 < h.data.size) :
    h.data[0]'hne ::ₘ (h.extractTail hne).elements = h.elements := by
  unfold MinHeap.extractTail
  split
  · have hlist : h.data.toList = [h.data[0]'hne] := by
      apply List.ext_get
      · simp
        omega
      · intro i hi₁ hi₂
        have hi : i = 0 := by
          simp at hi₂
          omega
        subst i
        simp [Array.getElem_toList]
    change h.data[0]'hne ::ₘ ((#[] : Array α).toList : Multiset α) =
      (h.data.toList : Multiset α)
    rw [hlist]
    rfl
  · have hsift := (siftDown_perm (moveLastToRoot h.data hne) 0).toList
    have hmove := moveLastToRoot_cons_perm h.data hne
    apply Multiset.coe_eq_coe.mpr
    exact (List.Perm.cons _ hsift).trans hmove

/-- **Extracting the minimum of a binary min-heap.** For a binary min-heap $h$ over a linearly
ordered type, extraction returns nothing when the level-order array of $h$ is empty. Otherwise it
returns the root entry (the first entry of the array) together with the heap obtained from $h$ by
removing its root and restoring heap order. -/
def MinHeap.extractMin {α : Type u} [LinearOrder α]
    (h : MinHeap α) : Option (α × MinHeap α) :=
  if hne : 0 < h.data.size then
    some (h.data[0]'hne, h.extractTail hne)
  else
    none

/-- **Extraction from a binary min-heap fails exactly when it is empty.** For a binary min-heap
$h$ over a linearly ordered type, extracting the minimum of $h$ returns no result if and only if
the level-order storage array of $h$ has size $0$. -/
theorem MinHeap.extractMin_eq_none_iff {α : Type u} [LinearOrder α]
    (h : MinHeap α) : h.extractMin = none ↔ h.data.size = 0 := by
  simp [MinHeap.extractMin]

/-- **The value extracted from a binary min-heap is one of its elements.** Let $h$ be a binary
min-heap over a linearly ordered type. If extracting the minimum from $h$ succeeds and returns a
value $x$ together with a heap $r$, then $x$ belongs to the multiset of elements of $h$. -/
theorem MinHeap.extractMin_mem {α : Type u} [LinearOrder α]
    {h : MinHeap α} {x : α} {rest : MinHeap α}
    (hx : h.extractMin = some (x, rest)) : x ∈ h.elements := by
  unfold MinHeap.extractMin at hx
  split at hx
  · simp only [Option.some.injEq, Prod.mk.injEq] at hx
    rcases hx with ⟨rfl, _⟩
    simp [MinHeap.elements, Array.mem_toList_iff]
  · contradiction

/-- **The value extracted from a binary min-heap is minimal.** Let $h$ be a binary min-heap over
a linearly ordered type. If extracting the minimum from $h$ succeeds and returns a value $x$
together with a heap $r$, then $x \le y$ for every value $y$ in the multiset of elements of $h$. -/
theorem MinHeap.extractMin_le {α : Type u} [LinearOrder α]
    {h : MinHeap α} {x y : α} {rest : MinHeap α}
    (hx : h.extractMin = some (x, rest)) (hy : y ∈ h.elements) : x ≤ y := by
  unfold MinHeap.extractMin at hx
  split at hx
  · simp only [Option.some.injEq, Prod.mk.injEq] at hx
    rcases hx with ⟨rfl, _⟩
    change y ∈ h.data.toList at hy
    rcases List.mem_iff_getElem.mp hy with ⟨i, hi, rfl⟩
    simpa using h.ordered.root_le i (by simpa using hi)
  · contradiction

/-- **Elements after binary heap extraction.** Let $h$ be a binary min-heap over a linearly ordered
type. If extracting the minimum of $h$ succeeds and returns the value $x$ and the heap $h'$, then
the multiset of elements of $h'$ is obtained from the multiset of elements of $h$ by erasing one
occurrence of $x$. -/
theorem MinHeap.extractMin_elements {α : Type u} [LinearOrder α]
    {h : MinHeap α} {x : α} {rest : MinHeap α}
    (hx : h.extractMin = some (x, rest)) :
    rest.elements = h.elements.erase x := by
  unfold MinHeap.extractMin at hx
  split at hx
  · simp only [Option.some.injEq, Prod.mk.injEq] at hx
    rcases hx with ⟨rfl, rfl⟩
    exact h.extractTail_elements _
  · contradiction

/-- **Binary heap extraction splits off the minimum.** Let $h$ be a binary min-heap over a linearly
ordered type. If extracting the minimum of $h$ succeeds and returns the value $x$ and the heap
$h'$, then the multiset of elements of $h$ equals the multiset of elements of $h'$ with one copy
of $x$ added.

The statement is phrased by adding $x$ back, not by erasing it from the multiset of $h$. -/
theorem MinHeap.extractMin_cons_elements {α : Type u} [LinearOrder α]
    {h : MinHeap α} {x : α} {rest : MinHeap α}
    (hx : h.extractMin = some (x, rest)) :
    x ::ₘ rest.elements = h.elements := by
  unfold MinHeap.extractMin at hx
  split at hx
  · simp only [Option.some.injEq, Prod.mk.injEq] at hx
    rcases hx with ⟨rfl, rfl⟩
    exact h.extractTail_cons_elements _
  · contradiction

/-- **Binary heap extraction removes one copy of the minimum.** Let $h$ be a binary min-heap over
a linearly ordered type. If extracting the minimum of $h$ succeeds and returns the value $x$ and
the heap $h'$, then the multiplicity of $x$ in the multiset of elements of $h'$ is its
multiplicity in the multiset of elements of $h$ minus one. -/
theorem MinHeap.extractMin_count {α : Type u} [LinearOrder α]
    {h : MinHeap α} {x : α} {rest : MinHeap α}
    (hx : h.extractMin = some (x, rest)) :
    Multiset.count x rest.elements = Multiset.count x h.elements - 1 := by
  have hc := congrArg (Multiset.count x) (h.extractMin_cons_elements hx)
  simp only [Multiset.count_cons] at hc
  simp at hc
  omega

/-- **Binary heap extraction leaves other multiplicities unchanged.** Let $h$ be a binary min-heap
over a linearly ordered type. If extracting the minimum of $h$ succeeds and returns the value $x$
and the heap $h'$, then every value $y \ne x$ occurs in the multiset of elements of $h'$ exactly
as many times as in the multiset of elements of $h$. -/
theorem MinHeap.extractMin_count_of_ne {α : Type u} [LinearOrder α]
    {h : MinHeap α} {x y : α} {rest : MinHeap α}
    (hx : h.extractMin = some (x, rest)) (hyx : y ≠ x) :
    Multiset.count y rest.elements = Multiset.count y h.elements := by
  have hc := congrArg (Multiset.count y) (h.extractMin_cons_elements hx)
  simpa only [Multiset.count_cons, ite_eq_right hyx, Nat.add_zero] using hc

/-- **Membership after extraction from a binary min-heap.** Let $h$ be a binary min-heap over a
linearly ordered type, and suppose extracting the minimum from $h$ succeeds and returns a value
$x$ together with a heap $r$. Then every value $y \ne x$ is an element of $r$ if and only if it
is an element of $h$. -/
theorem MinHeap.extractMin_mem_of_ne_iff {α : Type u} [LinearOrder α]
    {h : MinHeap α} {x y : α} {rest : MinHeap α}
    (hx : h.extractMin = some (x, rest)) (hyx : y ≠ x) :
    y ∈ rest.elements ↔ y ∈ h.elements := by
  rw [← h.extractMin_cons_elements hx]
  simp [hyx]

/-- **Extraction from a binary min-heap leaves a heap-ordered array.** Let $h$ be a binary
min-heap over a linearly ordered type. If extracting the minimum from $h$ succeeds and returns a
value $x$ together with a heap $r$, then the level-order array of $r$ is heap ordered: every
entry other than the root is at least its parent entry. -/
theorem MinHeap.extractMin_ordered {α : Type u} [LinearOrder α]
    {h : MinHeap α} {x : α} {rest : MinHeap α}
    (_hx : h.extractMin = some (x, rest)) : HeapOrdered rest.data := by
  exact rest.ordered

end Cslib.Algorithms.Lean
