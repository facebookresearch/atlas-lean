/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Multiset.AddSub

/-!
# Configurable-arity min-heaps

This file defines a min-heap backed by a contiguous level-order array. A requested arity below
two is normalized to two. For arity `d`, the parent of nonroot index `i` is `(i - 1) / d`, and
the child with zero-based offset `k` is `d * i + k + 1`.

Insertion appends once and sifts along the genuine `d`-ary ancestor path. Extraction moves the
last entry to the root and sifts it down along a single `d`-ary child path, choosing the smallest
valid child at each step. The representation stores exactly one array entry per multiset
occurrence, plus one natural-number arity field and proofs erased by Lean's compiler.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

set_option autoImplicit false

universe u

/-- Requested arities zero and one use the binary-heap policy. -/
def normalizedArity (requested : Nat) : Nat := max 2 requested

/-- Normalization always produces a valid heap arity. -/
theorem normalizedArity_valid (requested : Nat) : 2 ≤ normalizedArity requested := by
  simp [normalizedArity]

/-- A valid requested arity is unchanged by normalization. -/
@[simp] theorem normalizedArity_eq {d : Nat} (hd : 2 ≤ d) : normalizedArity d = d := by
  simp [normalizedArity, hd]

/-- The parent index in a contiguous level-order `d`-ary tree. -/
def daryParent (d i : Nat) : Nat := (i - 1) / d

/-- The child index with zero-based offset `k` in a contiguous `d`-ary tree. -/
def daryChild (d i k : Nat) : Nat := d * i + k + 1

/-- A child offset below `d` maps back to its parent. -/
theorem daryParent_child {d i k : Nat} (_hd : 2 ≤ d) (hk : k < d) :
    daryParent d (daryChild d i k) = i := by
  simp only [daryParent, daryChild]
  rw [show d * i + k + 1 - 1 = d * i + k by omega]
  apply Nat.div_eq_of_lt_le
  · simp [Nat.mul_comm]
  · simp only [Nat.add_mul]
    rw [Nat.mul_comm d i]
    omega

/-- The parent of a nonroot node has a strictly smaller index. -/
theorem daryParent_lt {d i : Nat} (_hd : 2 ≤ d) (hi : 0 < i) :
    daryParent d i < i := by
  unfold daryParent
  have hdiv : (i - 1) / d ≤ i - 1 := Nat.div_le_self _ _
  omega

/-- A nonroot node's parent is valid whenever the node is. -/
theorem daryParent_lt_size {α : Type u} (d : Nat) (hd : 2 ≤ d)
    (a : Array α) (i : Nat) (hi : i < a.size) (hpos : 0 < i) :
    daryParent d i < a.size :=
  (daryParent_lt hd hpos).trans hi

/-- Every valid nonroot node is no smaller than its immediate `d`-ary parent. -/
structure DaryHeapOrdered {α : Type u} [LE α] (d : Nat) (a : Array α) : Prop where
  arity_valid : 2 ≤ d
  parent_le : ∀ i (hi : i < a.size), (hpos : 0 < i) →
    a[daryParent d i]'(daryParent_lt_size d arity_valid a i hi hpos) ≤ a[i]

/-- The only potentially bad edge is the edge entering `i`. -/
structure DarySiftUpReady {α : Type u} [LE α]
    (d : Nat) (a : Array α) (i : Nat) : Prop where
  arity_valid : 2 ≤ d
  index_valid : i < a.size
  ordered_except : ∀ j (hj : j < a.size), (hjpos : 0 < j) → j ≠ i →
    a[daryParent d j]'(daryParent_lt_size d arity_valid a j hj hjpos) ≤ a[j]
  parent_below_children : ∀ j (hj : j < a.size), (hjpos : 0 < j) →
    daryParent d j = i → (hipos : 0 < i) →
    a[daryParent d i]'(daryParent_lt_size d arity_valid a i index_valid hipos) ≤ a[j]

/-- Repeatedly swap a value with its `d`-ary parent while it is smaller. -/
def darySiftUp {α : Type u} [LinearOrder α]
    (a : Array α) (i d : Nat) (hd : 2 ≤ d) : Array α :=
  if hi : i < a.size then
    if hpos : 0 < i then
      let p := daryParent d i
      if hlt : a[i] < a[p]'(daryParent_lt_size d hd a i hi hpos) then
        darySiftUp (a.swap i p hi (daryParent_lt_size d hd a i hi hpos)) p d hd
      else
        a
    else
      a
  else
    a
termination_by i
decreasing_by
  exact daryParent_lt hd hpos

/-- Sifting up only permutes the input array. -/
theorem darySiftUp_perm {α : Type u} [LinearOrder α]
    (a : Array α) (i d : Nat) (hd : 2 ≤ d) :
    (darySiftUp a i d hd).Perm a := by
  induction i using Nat.strong_induction_on generalizing a with
  | h i ih =>
    rw [darySiftUp]
    split
    · split
      · dsimp only
        split
        · exact (ih (daryParent d i) (daryParent_lt hd ‹0 < i›) _).trans
            (Array.swap_perm _ _)
        · exact Array.Perm.refl _
      · exact Array.Perm.refl _
    · exact Array.Perm.refl _

/-- Sifting up preserves the represented multiset. -/
theorem darySiftUp_multiset {α : Type u} [LinearOrder α]
    (a : Array α) (i d : Nat) (hd : 2 ≤ d) :
    (↑(darySiftUp a i d hd).toList : Multiset α) = (↑a.toList : Multiset α) :=
  Multiset.coe_eq_coe.mpr (darySiftUp_perm a i d hd).toList

/-- Local heap order implies that the root is no greater than any valid entry. -/
theorem DaryHeapOrdered.root_le {α : Type u} [LinearOrder α]
    {d : Nat} (hd : 2 ≤ d) {a : Array α} (h : DaryHeapOrdered d a)
    (i : Nat) (hi : i < a.size) : a[0]'(by omega) ≤ a[i] := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hzero : i = 0
    · subst i
      exact le_rfl
    · have hpos : 0 < i := by omega
      exact (ih (daryParent d i) (daryParent_lt hd hpos)
        (daryParent_lt_size d hd a i hi hpos)).trans (h.parent_le i hi hpos)

private theorem darySiftUpReady_swap {α : Type u} [LinearOrder α]
    (d : Nat) (a : Array α) (i : Nat) (h : DarySiftUpReady d a i)
    (hpos : 0 < i)
    (hlt : a[i]'h.index_valid <
      a[daryParent d i]'(daryParent_lt_size d h.arity_valid a i h.index_valid hpos)) :
    DarySiftUpReady d
      (a.swap i (daryParent d i) h.index_valid
        (daryParent_lt_size d h.arity_valid a i h.index_valid hpos))
      (daryParent d i) := by
  let p := daryParent d i
  have hp : p < a.size := daryParent_lt_size d h.arity_valid a i h.index_valid hpos
  have hpi : p < i := daryParent_lt h.arity_valid hpos
  refine {
    arity_valid := h.arity_valid
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
    · by_cases hparenti : daryParent d j = i
      · have hold := h.parent_below_children j hja hjpos hparenti hpos
        simpa only [Array.getElem_swap, hparenti, hji, hjp, p, ite_true, ite_false]
          using hold
      · by_cases hparentp : daryParent d j = p
        · have hold := h.ordered_except j hja hjpos hji
          have hold' : a[p]'hp ≤ a[j] := by simpa only [hparentp] using hold
          have hchain := hlt.le.trans hold'
          simpa only [Array.getElem_swap, hparenti, hparentp, hji, hjp, hpi.ne, p,
            ite_true, ite_false] using hchain
        · have hold := h.ordered_except j hja hjpos hji
          rw [Array.getElem_swap_of_ne hparenti hparentp,
            Array.getElem_swap_of_ne hji hjp]
          exact hold
  · intro j hj hjpos hparent hppos
    have hja : j < a.size := by simpa [p] using hj
    have hparent' : daryParent d j = p := by simpa [p] using hparent
    have hppos' : 0 < p := by simpa [p] using hppos
    have hpParentLt := daryParent_lt h.arity_valid hppos'
    have hppi : daryParent d p ≠ i := by omega
    by_cases hji : j = i
    · subst j
      have hold := h.ordered_except p hp hppos' (by omega)
      rw [Array.getElem_swap_of_ne hppi hpParentLt.ne, Array.getElem_swap_left]
      simpa only [p] using hold
    · have hjp : j ≠ p := by
        intro heq
        subst j
        exact (daryParent_lt h.arity_valid hppos').ne hparent'
      have hold := h.ordered_except j hja hjpos (by omega)
      have hold' : a[p]'hp ≤ a[j] := by simpa only [hparent'] using hold
      have parentEdge := h.ordered_except p hp hppos' (by omega)
      have hchain := parentEdge.trans hold'
      rw [Array.getElem_swap_of_ne hppi hpParentLt.ne,
        Array.getElem_swap_of_ne hji hjp]
      simpa only [p] using hchain

private theorem DarySiftUpReady.ordered_of_not_lt {α : Type u} [LinearOrder α]
    {d : Nat} {a : Array α} {i : Nat} (h : DarySiftUpReady d a i)
    (hpos : 0 < i)
    (hnlt : ¬a[i]'h.index_valid <
      a[daryParent d i]'(daryParent_lt_size d h.arity_valid a i h.index_valid hpos)) :
    DaryHeapOrdered d a := by
  refine { arity_valid := h.arity_valid, parent_le := ?_ }
  intro j hj hjpos
  if hji : j = i then
    subst j
    exact le_of_not_gt hnlt
  else
    exact h.ordered_except j hj hjpos hji

private theorem DarySiftUpReady.ordered_at_root {α : Type u} [LinearOrder α]
    {d : Nat} {a : Array α} (h : DarySiftUpReady d a 0) :
    DaryHeapOrdered d a := by
  refine { arity_valid := h.arity_valid, parent_le := ?_ }
  intro j hj hjpos
  exact h.ordered_except j hj hjpos (Nat.ne_of_gt hjpos)

/-- Sifting up one admissible incoming-edge violation restores heap order. -/
theorem darySiftUp_ordered {α : Type u} [LinearOrder α]
    (d : Nat) (a : Array α) (i : Nat) (h : DarySiftUpReady d a i) :
    DaryHeapOrdered d (darySiftUp a i d h.arity_valid) := by
  induction i using Nat.strong_induction_on generalizing a with
  | h i ih =>
    rw [darySiftUp]
    split
    · split
      · dsimp only
        split
        · have hlt' : a[i]'h.index_valid <
            a[daryParent d i]'(daryParent_lt_size d h.arity_valid a i
              h.index_valid ‹0 < i›) := by
            assumption
          apply ih (daryParent d i) (daryParent_lt h.arity_valid ‹0 < i›)
          exact darySiftUpReady_swap d a i h ‹0 < i› hlt'
        · exact h.ordered_of_not_lt ‹0 < i› (by assumption)
      · have hi0 : i = 0 := by omega
        subst i
        exact h.ordered_at_root
    · exact False.elim (‹¬i < a.size› h.index_valid)

/-- Appending to an ordered heap creates only the new entry's incoming-edge violation. -/
theorem daryPush_siftUpReady {α : Type u} [LinearOrder α]
    (d : Nat) (hd : 2 ≤ d) (a : Array α) (h : DaryHeapOrdered d a) (x : α) :
    DarySiftUpReady d (a.push x) a.size := by
  refine {
    arity_valid := hd
    index_valid := by simpa only [Array.size_push] using Nat.lt_succ_self a.size
    ordered_except := ?_
    parent_below_children := ?_
  }
  · intro j hj hjpos hjne
    have hjlt : j < a.size := by
      simp only [Array.size_push] at hj
      omega
    have hplt : daryParent d j < a.size := daryParent_lt_size d hd a j hjlt hjpos
    simpa only [Array.getElem_push_lt hjlt, Array.getElem_push_lt hplt] using
      h.parent_le j hjlt hjpos
  · intro j hj hjpos hp _
    have hpLt := daryParent_lt hd hjpos
    simp only [Array.size_push] at hj
    omega

/-- A child index is exactly a `daryChild` of its parent. -/
private theorem daryChild_of_parent {d i j : Nat} (hd : 2 ≤ d) (hjpos : 0 < j)
    (hp : daryParent d j = i) : ∃ k < d, j = daryChild d i k := by
  refine ⟨(j - 1) % d, Nat.mod_lt _ (by omega), ?_⟩
  have h := Nat.div_add_mod (j - 1) d
  simp only [daryParent] at hp
  rw [hp] at h
  simp only [daryChild]
  omega

/-- The only potentially bad edges leave `i`; lifting a smallest child to
`i` is safe for the edge entering `i`. -/
structure DarySiftDownReady {α : Type u} [LE α] (d : Nat) (a : Array α)
    (i : Nat) : Prop where
  arity_valid : 2 ≤ d
  index_valid : i < a.size
  ordered_except : ∀ j (hj : j < a.size), (hjpos : 0 < j) →
    daryParent d j ≠ i →
    a[daryParent d j]'(daryParent_lt_size d arity_valid a j hj hjpos) ≤ a[j]
  parent_below_children : ∀ j (hj : j < a.size), (hjpos : 0 < j) →
    daryParent d j = i → (hipos : 0 < i) →
    a[daryParent d i]'(daryParent_lt_size d arity_valid a i index_valid hipos) ≤
      a[j]

/-- Scan child offsets `start, start + 1, …, d - 1` and return the index of
a smallest valid child of `i`, if one exists. -/
def darySmallestChildFrom {α : Type u} [LinearOrder α]
    (a : Array α) (d i start : Nat) : Option Nat :=
  if hk : start < d then
    let c := daryChild d i start
    if hc : c < a.size then
      match darySmallestChildFrom a d i (start + 1) with
      | none => some c
      | some best =>
          if hbest : best < a.size then
            if a[best] < a[c] then some best else some c
          else
            some c
    else
      none
  else
    none
termination_by d - start
decreasing_by omega

/-- The smallest valid child of `i` in a `d`-ary heap, if one exists. -/
def darySmallestChild {α : Type u} [LinearOrder α]
    (a : Array α) (d i : Nat) : Option Nat :=
  darySmallestChildFrom a d i 0

/-- A selected child index is a valid array index. -/
private theorem darySmallestChildFrom_valid {α : Type u} [LinearOrder α]
    {a : Array α} {d i start c : Nat}
    (h : darySmallestChildFrom a d i start = some c) : c < a.size := by
  induction hn : d - start using Nat.strong_induction_on generalizing start c with
  | _ n ih =>
    unfold darySmallestChildFrom at h
    split at h
    · cases hrest : darySmallestChildFrom a d i (start + 1) with
      | none =>
          simp only [hrest] at h
          split at h
          · simp only [Option.some.injEq] at h
            subst h
            assumption
          · contradiction
      | some best =>
          simp only [hrest] at h
          split at h
          · split at h
            · split at h
              · simp only [Option.some.injEq] at h
                subst h
                exact ih _ (by omega) hrest rfl
              · simp only [Option.some.injEq] at h
                subst h
                assumption
            · simp only [Option.some.injEq] at h
              subst h
              assumption
          · contradiction
    · contradiction

/-- The smallest valid child of `i` is a valid array index. -/
theorem darySmallestChild_valid {α : Type u} [LinearOrder α]
    (a : Array α) (d i c : Nat) (h : darySmallestChild a d i = some c) :
    c < a.size :=
  darySmallestChildFrom_valid h

/-- A selected child has one of the scanned offsets as its child offset. -/
private theorem darySmallestChildFrom_offset {α : Type u} [LinearOrder α]
    {a : Array α} {d i start c : Nat}
    (h : darySmallestChildFrom a d i start = some c) :
    ∃ k, start ≤ k ∧ k < d ∧ c = daryChild d i k := by
  induction hn : d - start using Nat.strong_induction_on generalizing start c with
  | _ n ih =>
    unfold darySmallestChildFrom at h
    split at h
    · cases hrest : darySmallestChildFrom a d i (start + 1) with
      | none =>
          simp only [hrest] at h
          split at h
          · simp only [Option.some.injEq] at h
            subst h
            exact ⟨start, le_rfl, ‹start < d›, rfl⟩
          · contradiction
      | some best =>
          simp only [hrest] at h
          split at h
          · split at h
            · split at h
              · simp only [Option.some.injEq] at h
                subst h
                obtain ⟨k, hk1, hk2, hk3⟩ := ih _ (by omega) hrest rfl
                exact ⟨k, by omega, hk2, hk3⟩
              · simp only [Option.some.injEq] at h
                subst h
                exact ⟨start, le_rfl, ‹start < d›, rfl⟩
            · simp only [Option.some.injEq] at h
              subst h
              exact ⟨start, le_rfl, ‹start < d›, rfl⟩
          · contradiction
    · contradiction

/-- A selected child's parent is `i`. -/
private theorem darySmallestChild_parent {α : Type u} [LinearOrder α]
    {a : Array α} {d i c : Nat} (hd : 2 ≤ d)
    (h : darySmallestChild a d i = some c) : daryParent d c = i := by
  obtain ⟨k, -, hk, rfl⟩ := darySmallestChildFrom_offset h
  exact daryParent_child hd hk

/-- A selected child has a strictly larger index than its parent. -/
theorem darySmallestChild_gt {α : Type u} [LinearOrder α]
    {a : Array α} {d i c : Nat} (hd : 2 ≤ d)
    (h : darySmallestChild a d i = some c) : i < c := by
  obtain ⟨k, -, -, rfl⟩ := darySmallestChildFrom_offset h
  have hle : i ≤ d * i := Nat.le_mul_of_pos_left i (by omega)
  simp only [daryChild]
  omega

/-- A valid child in the scanned range guarantees a selection. -/
private theorem darySmallestChildFrom_isSome {α : Type u} [LinearOrder α]
    {a : Array α} {d i start k : Nat} (hstart : start ≤ k) (hk : k < d)
    (hc : daryChild d i k < a.size) :
    ∃ c, darySmallestChildFrom a d i start = some c := by
  induction hn : d - start using Nat.strong_induction_on generalizing start with
  | _ n ih =>
    unfold darySmallestChildFrom
    by_cases hstartd : start < d
    · rw [dite_eq_left hstartd]
      by_cases hcase : start = k
      · subst k
        rw [dite_eq_left hc]
        cases hrest : darySmallestChildFrom a d i (start + 1) with
        | none => exact ⟨daryChild d i start, by simp⟩
        | some best =>
            by_cases hbest : best < a.size
            · by_cases hcmp : a[best]'hbest < a[daryChild d i start]'hc
              · exact ⟨best, by simp [hbest, hcmp]⟩
              · exact ⟨daryChild d i start, by simp [hbest, hcmp]⟩
            · exact ⟨daryChild d i start, by simp [hbest]⟩
      · have hcstart : daryChild d i start < a.size := by
          by_contra hcon
          have hge : daryChild d i start ≤ daryChild d i k := by
            simp only [daryChild]
            omega
          omega
        rw [dite_eq_left hcstart]
        obtain ⟨c, hc'⟩ := ih (start := start + 1) _ (by omega) (by omega) rfl
        by_cases hbest : c < a.size
        · by_cases hcmp : a[c]'hbest < a[daryChild d i start]'hcstart
          · exact ⟨c, by simp [hc', hbest, hcmp]⟩
          · exact ⟨daryChild d i start, by simp [hc', hbest, hcmp]⟩
        · exact ⟨daryChild d i start, by simp [hc', hbest]⟩
    · omega

/-- The selected child is no greater than any scanned valid child. -/
private theorem darySmallestChildFrom_le {α : Type u} [LinearOrder α]
    {a : Array α} {d i start c : Nat}
    (h : darySmallestChildFrom a d i start = some c) :
    ∀ (k : Nat) (_hk : start ≤ k) (_hkd : k < d)
      (hc : daryChild d i k < a.size) (hcv : c < a.size),
      a[c]'hcv ≤ a[daryChild d i k]'hc := by
  induction hn : d - start using Nat.strong_induction_on generalizing start c with
  | _ n ih =>
    intro k hk hkd hc hcv
    unfold darySmallestChildFrom at h
    split at h
    · cases hrest : darySmallestChildFrom a d i (start + 1) with
      | none =>
          simp only [hrest] at h
          split at h
          · simp only [Option.some.injEq] at h
            subst h
            by_cases hcase : k = start
            · subst k
              exact le_rfl
            · exfalso
              obtain ⟨c', hc'⟩ :=
                darySmallestChildFrom_isSome (a := a) (d := d) (i := i)
                  (start := start + 1) (k := k) (by omega) hkd hc
              rw [hc'] at hrest
              contradiction
          · contradiction
      | some best =>
          simp only [hrest] at h
          have hbestv : best < a.size := darySmallestChildFrom_valid hrest
          have ihle := ih _ (by omega) hrest rfl
          by_cases hc0 : daryChild d i start < a.size
          · rw [dite_eq_left hc0] at h
            by_cases hbest0 : best < a.size
            · rw [dite_eq_left hbest0] at h
              by_cases hcmp : a[best]'hbest0 < a[daryChild d i start]'hc0
              · rw [ite_eq_left hcmp] at h
                simp only [Option.some.injEq] at h
                subst h
                by_cases hcase : k = start
                · subst k
                  exact le_of_lt hcmp
                · exact ihle k (by omega) hkd hc hbestv
              · rw [ite_eq_right hcmp] at h
                simp only [Option.some.injEq] at h
                subst h
                by_cases hcase : k = start
                · subst k
                  exact le_rfl
                · exact (le_of_not_gt hcmp).trans
                    (ihle k (by omega) hkd hc hbestv)
            · rw [dite_eq_right hbest0] at h
              simp only [Option.some.injEq] at h
              subst h
              by_cases hcase : k = start
              · subst k
                exact le_rfl
              · exfalso
                exact hbest0 hbestv
          · rw [dite_eq_right hc0] at h
            contradiction
    · contradiction

/-- The smallest child is no greater than every valid child of `i`. -/
private theorem darySmallestChild_le {α : Type u} [LinearOrder α]
    (a : Array α) (d i c : Nat) (hd : 2 ≤ d)
    (h : darySmallestChild a d i = some c)
    (j : Nat) (hj : j < a.size) (hjpos : 0 < j) (hp : daryParent d j = i) :
    a[c]'(darySmallestChild_valid a d i c h) ≤ a[j]'(by
      exact hj) := by
  obtain ⟨k, hkd, rfl⟩ := daryChild_of_parent hd hjpos hp
  exact darySmallestChildFrom_le h k (Nat.zero_le k) hkd hj
    (darySmallestChild_valid a d i c h)

/-- Repeatedly swap a value with its smallest `d`-ary child while that
child is smaller. -/
def darySiftDown {α : Type u} [LinearOrder α]
    (a : Array α) (i d : Nat) (hd : 2 ≤ d) : Array α :=
  match hchild : darySmallestChild a d i with
  | none => a
  | some c =>
    have hc : c < a.size := darySmallestChild_valid a d i c hchild
    have hi : i < a.size := (darySmallestChild_gt hd hchild).trans hc
    if hlt : a[c] < a[i] then
      darySiftDown (a.swap i c hi hc) c d hd
    else
      a
termination_by a.size - i
decreasing_by
  simp only [Array.size_swap]
  have := darySmallestChild_gt hd hchild
  omega

/-- Sifting down only permutes the input array. -/
theorem darySiftDown_perm {α : Type u} [LinearOrder α]
    (a : Array α) (i d : Nat) (hd : 2 ≤ d) :
    (darySiftDown a i d hd).Perm a := by
  induction hm : a.size - i using Nat.strong_induction_on generalizing a i with
  | h n ih =>
    rw [darySiftDown]
    split
    · exact Array.Perm.refl _
    · rename_i c hchild
      dsimp only
      split
      · have hc : c < a.size := darySmallestChild_valid a d i c hchild
        have hgt : i < c := darySmallestChild_gt hd hchild
        have hi : i < a.size := hgt.trans hc
        have hdec : (a.swap i c hi hc).size - c < n := by
            simp only [Array.size_swap]
            rw [← hm]
            omega
        exact (ih _ hdec (a.swap i c hi hc) c rfl).trans
          (Array.swap_perm hi hc)
      · exact Array.Perm.refl _

/-- Sifting down preserves the represented multiset. -/
theorem darySiftDown_multiset {α : Type u} [LinearOrder α]
    (a : Array α) (i d : Nat) (hd : 2 ≤ d) :
    (↑(darySiftDown a i d hd).toList : Multiset α) = (↑a.toList : Multiset α) :=
  Multiset.coe_eq_coe.mpr (darySiftDown_perm a i d hd).toList

private theorem darySiftDownReady_swap {α : Type u} [LinearOrder α]
    (a : Array α) (d i c : Nat) (hchild : darySmallestChild a d i = some c)
    (h : DarySiftDownReady d a i)
    (hlt : a[c]'(darySmallestChild_valid a d i c hchild) < a[i]'h.index_valid) :
    DarySiftDownReady d
      (a.swap i c h.index_valid (darySmallestChild_valid a d i c hchild)) c := by
  have hd : 2 ≤ d := h.arity_valid
  have hc : c < a.size := darySmallestChild_valid a d i c hchild
  have hic : i < c := darySmallestChild_gt hd hchild
  have hpci : daryParent d c = i := darySmallestChild_parent hd hchild
  refine {
    arity_valid := hd
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
        have hparent_ne_c : daryParent d i ≠ c := by
          have := daryParent_lt hd hipos
          omega
        have hparent_ne_i : daryParent d i ≠ i := (daryParent_lt hd hipos).ne
        rw [Array.getElem_swap_of_ne hparent_ne_i hparent_ne_c,
          Array.getElem_swap_left]
        exact hold
      · by_cases hparenti : daryParent d j = i
        · have hold := darySmallestChild_le a d i c hd hchild j hja hjpos hparenti
          simpa only [Array.getElem_swap, hparenti, hji, hjc, hic.ne, ite_true,
            ite_false] using hold
        · have hold := h.ordered_except j hja hjpos hparenti
          have hparent_ne_c : daryParent d j ≠ c := hparentc
          rw [Array.getElem_swap_of_ne hparenti hparent_ne_c,
            Array.getElem_swap_of_ne hji hjc]
          exact hold
  · intro j hj hjpos hparent hcp
    have hja : j < a.size := by simpa using hj
    have hparent' : daryParent d j = c := by simpa using hparent
    have hjc : j ≠ c := by
      intro heq
      subst j
      exact (daryParent_lt hd hcp).ne hparent'
    have hcj : c < j := by
      rw [← hparent']
      exact daryParent_lt hd hjpos
    have hji : j ≠ i := by omega
    have hold := h.ordered_except j hja hjpos (by omega)
    have hold' : a[c]'hc ≤ a[j] := by simpa only [hparent'] using hold
    simpa only [Array.getElem_swap, hpci, hji, hjc, hic.ne, ite_true, ite_false]
      using hold'

private theorem dary_no_child_ordered {α : Type u} [LinearOrder α]
    {d : Nat} {a : Array α} {i : Nat} (h : DarySiftDownReady d a i)
    (hnone : darySmallestChild a d i = none) : DaryHeapOrdered d a := by
  have hchild0 : ¬daryChild d i 0 < a.size := by
    intro hc
    obtain ⟨c, hc'⟩ := darySmallestChildFrom_isSome (a := a) (d := d) (i := i)
      (start := 0) (k := 0) (Nat.zero_le 0) (by have hv := h.arity_valid; omega) hc
    change darySmallestChildFrom a d i 0 = none at hnone
    rw [hc'] at hnone
    contradiction
  refine { arity_valid := h.arity_valid, parent_le := ?_ }
  intro j hj hjpos
  by_cases hp : daryParent d j = i
  · obtain ⟨k, -, rfl⟩ := daryChild_of_parent h.arity_valid hjpos hp
    exact (hchild0 ((by simp only [daryChild]; omega : daryChild d i 0 ≤
      daryChild d i k).trans_lt hj)).elim
  · exact h.ordered_except j hj hjpos hp

private theorem dary_no_swap_ordered {α : Type u} [LinearOrder α]
    {d : Nat} {a : Array α} {i c : Nat} (h : DarySiftDownReady d a i)
    (hchild : darySmallestChild a d i = some c)
    (hnlt : ¬a[c]'(darySmallestChild_valid a d i c hchild) < a[i]'h.index_valid) :
    DaryHeapOrdered d a := by
  refine { arity_valid := h.arity_valid, parent_le := ?_ }
  intro j hj hjpos
  by_cases hp : daryParent d j = i
  · have hbase :=
      (le_of_not_gt hnlt).trans
        (darySmallestChild_le a d i c h.arity_valid hchild j hj hjpos hp)
    simpa only [hp] using hbase
  · exact h.ordered_except j hj hjpos hp

/-- Sifting down an array with admissible outgoing-edge violations restores
the local `d`-ary heap-order invariant. -/
theorem darySiftDown_ordered {α : Type u} [LinearOrder α]
    (d : Nat) (a : Array α) (i : Nat) (hd : 2 ≤ d)
    (h : DarySiftDownReady d a i) :
    DaryHeapOrdered d (darySiftDown a i d hd) := by
  induction hm : a.size - i using Nat.strong_induction_on generalizing a i with
  | h n ih =>
    rw [darySiftDown]
    split
    · rename_i hchild
      exact dary_no_child_ordered h hchild
    · rename_i c hchild
      dsimp only
      split
      · have hlt' : a[c]'(darySmallestChild_valid a d i c hchild) <
            a[i]'h.index_valid := by
          assumption
        have hready := darySiftDownReady_swap a d i c hchild h hlt'
        have hdec : (a.swap i c h.index_valid
            (darySmallestChild_valid a d i c hchild)).size - c < n := by
          simp only [Array.size_swap]
          rw [← hm]
          have := darySmallestChild_gt hd hchild
          have := darySmallestChild_valid a d i c hchild
          have := h.index_valid
          omega
        exact ih _ hdec _ _ hready rfl
      · have hnlt' :
            ¬a[c]'(darySmallestChild_valid a d i c hchild) < a[i]'h.index_valid := by
          assumption
        exact dary_no_swap_ordered h hchild hnlt'

/-- Move the last entry to the root and remove the old root. -/
def daryMoveLastToRoot {α : Type u} (a : Array α) (hne : 0 < a.size) :
    Array α :=
  (a.swap 0 (a.size - 1) hne (by omega)).pop

/-- Last-to-root replacement creates exactly an admissible sift-down
violation at the root whenever at least two entries were present. -/
theorem daryMoveLastToRoot_siftDownReady {α : Type u} [LinearOrder α]
    (d : Nat) (a : Array α) (h : DaryHeapOrdered d a) (htwo : 1 < a.size) :
    DarySiftDownReady d (daryMoveLastToRoot a (by omega)) 0 := by
  let last := a.size - 1
  have hzero : 0 < a.size := by omega
  have hlast : last < a.size := by omega
  refine {
    arity_valid := h.arity_valid
    index_valid := by simp [daryMoveLastToRoot]; omega
    ordered_except := ?_
    parent_below_children := ?_
  }
  · intro j hj hjpos hpzero
    have hjlt : j < a.size - 1 := by
      simpa [daryMoveLastToRoot] using hj
    have hja : j < a.size := by omega
    have hjlast : j ≠ last := by omega
    have hparentlast : daryParent d j ≠ last := by
      have := daryParent_lt h.arity_valid hjpos
      omega
    have hold := h.parent_le j hja hjpos
    simpa only [daryMoveLastToRoot, Array.getElem_pop, Array.getElem_swap, last,
      hpzero, hjlast, hparentlast, ne_of_gt hjpos, ite_false] using hold
  · intro _ _ _ _ hzero'
    omega

private theorem daryMoveLastToRoot_cons_perm {α : Type u} [LinearOrder α]
    (a : Array α) (hne : 0 < a.size) :
    (a[0]'hne :: (daryMoveLastToRoot a hne).toList).Perm a.toList := by
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
  simpa [daryMoveLastToRoot, b, Array.toList_pop] using hperm.trans hswap

/-- Last-to-root replacement removes exactly one occurrence of the old root. -/
theorem daryMoveLastToRoot_elements {α : Type u} [LinearOrder α]
    (a : Array α) (hne : 0 < a.size) :
    (↑(daryMoveLastToRoot a hne).toList : Multiset α) =
      (↑a.toList : Multiset α).erase (a[0]'hne) := by
  have hp := daryMoveLastToRoot_cons_perm a hne
  have hm : a[0]'hne ::ₘ (↑(daryMoveLastToRoot a hne).toList : Multiset α) =
      (↑a.toList : Multiset α) := Multiset.coe_eq_coe.mpr hp
  rw [← hm, Multiset.erase_cons_head]

/-- A configurable-arity min-heap with a contiguous level-order representation. -/
structure DaryMinHeap (α : Type u) [LinearOrder α] where
  /-- The normalized arity, always at least two. -/
  arity : Nat
  arity_valid : 2 ≤ arity
  /-- The level-order storage array. -/
  data : Array α
  ordered : DaryHeapOrdered arity data

/-- The multiset represented by a heap. -/
def DaryMinHeap.elements {α : Type u} [LinearOrder α]
    (h : DaryMinHeap α) : Multiset α := h.data.toList

/-- The empty heap, normalizing a requested arity below two to two. -/
def DaryMinHeap.empty {α : Type u} [LinearOrder α]
    (requestedArity : Nat) : DaryMinHeap α where
  arity := normalizedArity requestedArity
  arity_valid := normalizedArity_valid requestedArity
  data := #[]
  ordered := {
    arity_valid := normalizedArity_valid requestedArity
    parent_le := by simp
  }

/-- Insert one value, repairing only its arity-dependent ancestor path. -/
def DaryMinHeap.push {α : Type u} [LinearOrder α]
    (h : DaryMinHeap α) (x : α) : DaryMinHeap α where
  arity := h.arity
  arity_valid := h.arity_valid
  data := darySiftUp (h.data.push x) h.data.size h.arity h.arity_valid
  ordered := darySiftUp_ordered h.arity _ _
    (daryPush_siftUpReady h.arity h.arity_valid h.data h.ordered x)

/-- Inspect the minimum without removing it. -/
def DaryMinHeap.min? {α : Type u} [LinearOrder α]
    (h : DaryMinHeap α) : Option α := h.data[0]?

/-- Inspection fails exactly for the empty representation. -/
theorem DaryMinHeap.min?_eq_none_iff {α : Type u} [LinearOrder α]
    (h : DaryMinHeap α) : h.min? = none ↔ h.data.size = 0 := by
  simp [DaryMinHeap.min?, getElem?_def]

/-- Inspection returns a stored value. -/
theorem DaryMinHeap.min?_mem {α : Type u} [LinearOrder α]
    {h : DaryMinHeap α} {x : α} (hx : h.min? = some x) : x ∈ h.elements := by
  unfold DaryMinHeap.min? at hx
  simp only [getElem?_def] at hx
  split at hx
  · simp only [Option.some.injEq] at hx
    subst x
    simp [DaryMinHeap.elements, Array.mem_toList_iff]
  · contradiction

/-- Inspection returns a value no greater than every represented value. -/
theorem DaryMinHeap.min?_le {α : Type u} [LinearOrder α]
    {h : DaryMinHeap α} {x y : α} (hx : h.min? = some x) (hy : y ∈ h.elements) :
    x ≤ y := by
  unfold DaryMinHeap.min? at hx
  simp only [getElem?_def] at hx
  split at hx
  · simp only [Option.some.injEq] at hx
    subst x
    change y ∈ h.data.toList at hy
    rcases List.mem_iff_getElem.mp hy with ⟨i, hi, rfl⟩
    simpa using h.ordered.root_le h.arity_valid i (by simpa using hi)
  · contradiction

/-- Insertion adds exactly one multiset occurrence. -/
theorem DaryMinHeap.elements_push {α : Type u} [LinearOrder α]
    (h : DaryMinHeap α) (x : α) :
    (h.push x).elements = x ::ₘ h.elements := by
  have hp := (darySiftUp_perm (h.data.push x) h.data.size h.arity h.arity_valid).toList
  rw [Array.toList_push] at hp
  apply Multiset.coe_eq_coe.mpr
  exact hp.trans List.perm_append_comm

/-- Insertion preserves local `d`-ary heap order. -/
theorem DaryMinHeap.push_ordered {α : Type u} [LinearOrder α]
    (h : DaryMinHeap α) (x : α) :
    DaryHeapOrdered h.arity (h.push x).data :=
  (h.push x).ordered

/-- Inserting a value raises its multiplicity by one. -/
theorem DaryMinHeap.count_push_self {α : Type u} [LinearOrder α]
    (h : DaryMinHeap α) (x : α) :
    Multiset.count x (h.push x).elements = Multiset.count x h.elements + 1 := by
  rw [h.elements_push x]
  simp

/-- Insertion preserves every different value's multiplicity. -/
theorem DaryMinHeap.count_push_of_ne {α : Type u} [LinearOrder α]
    (h : DaryMinHeap α) {x y : α} (hyx : y ≠ x) :
    Multiset.count y (h.push x).elements = Multiset.count y h.elements := by
  rw [h.elements_push x]
  simp [hyx]

/-- Remove the root from a known nonempty heap and restore heap order:
the last entry moves to the root and sifts down its `d`-ary child path. -/
def DaryMinHeap.extractTail {α : Type u} [LinearOrder α]
    (h : DaryMinHeap α) (hne : 0 < h.data.size) : DaryMinHeap α :=
  if hone : h.data.size = 1 then
    ⟨h.arity, h.arity_valid, #[], {
      arity_valid := h.arity_valid
      parent_le := by simp
    }⟩
  else
    have htwo : 1 < h.data.size := by omega
    let moved := daryMoveLastToRoot h.data hne
    ⟨h.arity, h.arity_valid, darySiftDown moved 0 h.arity h.arity_valid,
      darySiftDown_ordered h.arity moved 0 h.arity_valid
        (daryMoveLastToRoot_siftDownReady h.arity h.data h.ordered htwo)⟩

/-- Extraction preserves the heap arity. -/
theorem DaryMinHeap.extractTail_arity {α : Type u} [LinearOrder α]
    (h : DaryMinHeap α) (hne : 0 < h.data.size) :
    (h.extractTail hne).arity = h.arity := by
  unfold DaryMinHeap.extractTail
  split <;> rfl

private theorem DaryMinHeap.extractTail_elements {α : Type u} [LinearOrder α]
    (h : DaryMinHeap α) (hne : 0 < h.data.size) :
    (h.extractTail hne).elements = h.elements.erase (h.data[0]'hne) := by
  unfold DaryMinHeap.extractTail
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
  · have hp := (darySiftDown_perm (daryMoveLastToRoot h.data hne) 0
      h.arity h.arity_valid).toList
    have hm :
        (↑(darySiftDown (daryMoveLastToRoot h.data hne) 0 h.arity
          h.arity_valid).toList : Multiset α) =
        (↑(daryMoveLastToRoot h.data hne).toList : Multiset α) :=
      Multiset.coe_eq_coe.mpr hp
    change (↑(darySiftDown (daryMoveLastToRoot h.data hne) 0 h.arity
        h.arity_valid).toList : Multiset α) =
      (↑h.data.toList : Multiset α).erase (h.data[0]'hne)
    exact hm.trans (daryMoveLastToRoot_elements h.data hne)

private theorem DaryMinHeap.extractTail_cons_elements {α : Type u}
    [LinearOrder α] (h : DaryMinHeap α) (hne : 0 < h.data.size) :
    h.data[0]'hne ::ₘ (h.extractTail hne).elements = h.elements := by
  unfold DaryMinHeap.extractTail
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
  · have hsift := (darySiftDown_perm (daryMoveLastToRoot h.data hne) 0
      h.arity h.arity_valid).toList
    have hmove := daryMoveLastToRoot_cons_perm h.data hne
    apply Multiset.coe_eq_coe.mpr
    exact (List.Perm.cons _ hsift).trans hmove

/-- Build a heap by genuine arity-dependent insertions. -/
def DaryMinHeap.ofList {α : Type u} [LinearOrder α]
    (requestedArity : Nat) : List α → DaryMinHeap α
  | [] => DaryMinHeap.empty requestedArity
  | x :: xs => (DaryMinHeap.ofList requestedArity xs).push x

/-- Building from a list preserves every occurrence. -/
theorem DaryMinHeap.elements_ofList {α : Type u} [LinearOrder α]
    (requestedArity : Nat) (xs : List α) :
    (DaryMinHeap.ofList requestedArity xs).elements = (↑xs : Multiset α) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [DaryMinHeap.ofList, DaryMinHeap.elements_push, ih]
    rfl

/-- Building from a list uses the normalized requested arity. -/
theorem DaryMinHeap.arity_ofList {α : Type u} [LinearOrder α]
    (requestedArity : Nat) (xs : List α) :
    (DaryMinHeap.ofList requestedArity xs).arity = normalizedArity requestedArity := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [DaryMinHeap.ofList, DaryMinHeap.push] using ih

/-- Remove and return the minimum. The last entry moves to the root and
sifts down, so extraction follows one `d`-ary child path. -/
def DaryMinHeap.extractMin {α : Type u} [LinearOrder α]
    (h : DaryMinHeap α) : Option (α × DaryMinHeap α) :=
  if hne : 0 < h.data.size then
    some (h.data[0]'hne, h.extractTail hne)
  else
    none

/-- Extraction fails exactly for the empty representation. -/
theorem DaryMinHeap.extractMin_eq_none_iff {α : Type u} [LinearOrder α]
    (h : DaryMinHeap α) : h.extractMin = none ↔ h.data.size = 0 := by
  simp [DaryMinHeap.extractMin]

/-- A successful extraction partitions the represented multiset exactly. -/
theorem DaryMinHeap.extractMin_cons_elements {α : Type u} [LinearOrder α]
    {h : DaryMinHeap α} {x : α} {rest : DaryMinHeap α}
    (hx : h.extractMin = some (x, rest)) :
    x ::ₘ rest.elements = h.elements := by
  unfold DaryMinHeap.extractMin at hx
  split at hx
  · simp only [Option.some.injEq, Prod.mk.injEq] at hx
    rcases hx with ⟨rfl, rfl⟩
    exact h.extractTail_cons_elements _
  · contradiction

/-- A successful extraction erases exactly one occurrence of its result. -/
theorem DaryMinHeap.extractMin_elements {α : Type u} [LinearOrder α]
    {h : DaryMinHeap α} {x : α} {rest : DaryMinHeap α}
    (hx : h.extractMin = some (x, rest)) :
    rest.elements = h.elements.erase x := by
  rw [← h.extractMin_cons_elements hx, Multiset.erase_cons_head]

/-- Successful extraction decreases the result's multiplicity by one. -/
theorem DaryMinHeap.extractMin_count {α : Type u} [LinearOrder α]
    {h : DaryMinHeap α} {x : α} {rest : DaryMinHeap α}
    (hx : h.extractMin = some (x, rest)) :
    Multiset.count x rest.elements = Multiset.count x h.elements - 1 := by
  have hc := congrArg (Multiset.count x) (h.extractMin_cons_elements hx)
  simp only [Multiset.count_cons] at hc
  simp at hc
  omega

/-- A successful extraction returns a stored value. -/
theorem DaryMinHeap.extractMin_mem {α : Type u} [LinearOrder α]
    {h : DaryMinHeap α} {x : α} {rest : DaryMinHeap α}
    (hx : h.extractMin = some (x, rest)) : x ∈ h.elements := by
  rw [← h.extractMin_cons_elements hx]
  simp

/-- A successful extraction returns a globally minimal stored value. -/
theorem DaryMinHeap.extractMin_le {α : Type u} [LinearOrder α]
    {h : DaryMinHeap α} {x y : α} {rest : DaryMinHeap α}
    (hx : h.extractMin = some (x, rest)) (hy : y ∈ h.elements) : x ≤ y := by
  unfold DaryMinHeap.extractMin at hx
  split at hx
  · simp only [Option.some.injEq, Prod.mk.injEq] at hx
    rcases hx with ⟨rfl, rfl⟩
    change y ∈ h.data.toList at hy
    rcases List.mem_iff_getElem.mp hy with ⟨i, hi, rfl⟩
    simpa using h.ordered.root_le h.arity_valid i (by simpa using hi)
  · contradiction

/-- A successful extraction preserves the heap arity. -/
theorem DaryMinHeap.extractMin_arity {α : Type u} [LinearOrder α]
    {h : DaryMinHeap α} {x : α} {rest : DaryMinHeap α}
    (hx : h.extractMin = some (x, rest)) : rest.arity = h.arity := by
  unfold DaryMinHeap.extractMin at hx
  split at hx
  · simp only [Option.some.injEq, Prod.mk.injEq] at hx
    rcases hx with ⟨rfl, rfl⟩
    exact h.extractTail_arity _
  · contradiction

/-- Every returned heap satisfies its local heap-order invariant. -/
theorem DaryMinHeap.extractMin_ordered {α : Type u} [LinearOrder α]
    {h : DaryMinHeap α} {x : α} {rest : DaryMinHeap α}
    (_hx : h.extractMin = some (x, rest)) :
    DaryHeapOrdered rest.arity rest.data :=
  rest.ordered

/-- The backing array stores exactly one entry per represented occurrence. -/
theorem DaryMinHeap.card_elements {α : Type u} [LinearOrder α]
    (h : DaryMinHeap α) : h.elements.card = h.data.size := by
  simp [DaryMinHeap.elements]

end Cslib.Algorithms.Lean
