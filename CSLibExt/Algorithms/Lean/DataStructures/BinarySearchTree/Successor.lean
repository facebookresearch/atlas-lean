/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree

/-!
# Successor and predecessor queries in binary search trees

The successor of a key `x` is the least stored key strictly greater than `x`, and the
predecessor the greatest stored key strictly smaller than `x`; each is `none` exactly
when no such key exists. Like `rank` and `select`, these are traversal specifications
via the inorder traversal; they claim no navigation cost.
-/

set_option autoImplicit false

universe u

@[expose] public section

namespace Cslib.Algorithms.Lean
namespace BinarySearchTree

/-- Decidable membership in a binary tree, by structural recursion. Needed to elaborate
the `if x ∈ tree` test in `successor`; it must be public because a public definition
cannot reference a private declaration. -/
public instance instDecidableMemBinaryTree_cSLibExt {α : Type u} [LinearOrder α] (x : α)
    (tree : BinaryTree α) :
    Decidable (x ∈ tree) :=
  match tree with
  | .nil => isFalse (by simp)
  | .node key left right =>
      match instDecidableMemBinaryTree_cSLibExt x left, decEq x key,
        instDecidableMemBinaryTree_cSLibExt x right with
      | isTrue h1, _, _ => isTrue (mem_node.mpr (Or.inl h1))
      | _, isTrue h2, _ => isTrue (mem_node.mpr (Or.inr (Or.inl h2)))
      | _, _, isTrue h3 => isTrue (mem_node.mpr (Or.inr (Or.inr h3)))
      | isFalse h1, isFalse h2, isFalse h3 =>
          isFalse (by simp [mem_node, h1, h2, h3])

/-- **Successor in a binary search tree.** For a linearly ordered type `α`, a key
`x` and a binary tree `t`, the successor of `x` in `t` is the entry of the
inorder traversal of `t` at the position `rank x t` advanced past `x` itself
when present; equivalently the least key of `t` strictly greater than `x` on
ordered trees. This is a traversal specification; it claims no navigation cost. -/
public def successor {α : Type u} [LinearOrder α] (x : α) (tree : BinaryTree α) : Option α :=
  select tree (rank x tree + if x ∈ tree then 1 else 0)

private theorem filter_lt_nil_of_forall_gt {α : Type u} [LinearOrder α] {a : α}
    {xs : List α} (h : ∀ x ∈ xs, a < x) : xs.filter (· < a) = [] := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    have hab : a < b := h b (by simp)
    have hbs : ∀ x ∈ bs, a < x := by
      intro x hx
      exact h x (by simp [hx])
    simp [not_lt_of_ge (le_of_lt hab), ih hbs]

private theorem head_le_of_pairwise {α : Type u} [LinearOrder α] {b : α} {bs : List α}
    (h : List.Pairwise (· < ·) (b :: bs)) {z : α} (hz : z ∈ b :: bs) : b ≤ z := by
  rw [List.pairwise_cons] at h
  rcases h with ⟨hb, -⟩
  rw [List.mem_cons] at hz
  rcases hz with rfl | hz
  · exact le_rfl
  · exact le_of_lt (hb z hz)

private theorem succSome_of_mem {α : Type u} [LinearOrder α] {x y : α} {xs : List α}
    (hxs : List.Pairwise (· < ·) xs) (hx : x ∈ xs) :
    xs[((xs.filter (· < x)).length) + 1]? = some y ↔
      y ∈ xs ∧ x < y ∧ ∀ z ∈ xs, x < z → y ≤ z := by
  induction xs with
  | nil => simp at hx
  | cons a as ih =>
      rw [List.pairwise_cons] at hxs
      rcases hxs with ⟨ha, has⟩
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · -- The queried key is the head: the successor is the head of the tail.
        have hflt : (x :: as).filter (· < x) = [] := by
          have h1 : ¬ x < x := lt_irrefl x
          have h2 : (x :: as).filter (· < x) = as.filter (· < x) := by simp [h1]
          rw [h2]
          exact filter_lt_nil_of_forall_gt ha
        have hlen : (((x :: as).filter (· < x)).length) = 0 := by simp [hflt]
        rw [hlen]
        clear ih
        revert ha has
        cases as with
        | nil =>
            intro has ha
            have hnil : (x :: ([] : List α))[0 + 1]? = none := rfl
            rw [hnil]
            constructor
            · intro h
              simp at h
            · rintro ⟨hy, hxy, -⟩
              simp at hy
              rw [hy] at hxy
              exact absurd hxy (lt_irrefl x)
        | cons b bs =>
            intro has ha
            have hcons : (x :: b :: bs)[0 + 1]? = some b := rfl
            rw [hcons]
            constructor
            · intro h
              have hby : b = y := by simpa using h
              subst hby
              refine ⟨by simp, ha b (by simp), ?_⟩
              intro z hz haz
              rw [List.mem_cons] at hz
              rcases hz with hz | hz
              · rw [hz] at haz
                exact absurd haz (lt_irrefl x)
              · exact head_le_of_pairwise has hz
            · rintro ⟨hy, hxy, hmin⟩
              have hy' : y ∈ b :: bs := by
                rw [List.mem_cons] at hy
                rcases hy with hy | hy
                · rw [hy] at hxy
                  exact absurd hxy (lt_irrefl x)
                · exact hy
              have hby : b ≤ y := head_le_of_pairwise has hy'
              have hyb : y ≤ b := hmin b (by simp) (ha b (by simp))
              have hyb' : y = b := le_antisymm hyb hby
              simp [hyb']
      · -- The queried key is in the tail: strip the head.
        have hax : a < x := ha x hx
        have hlen : (((a :: as).filter (· < x)).length)
            = ((as.filter (· < x)).length) + 1 := by simp [hax]
        simp only [hlen, List.getElem?_cons_succ, ih has hx]
        constructor
        · rintro ⟨hy, hxy, hmin⟩
          refine ⟨List.mem_cons.mpr (Or.inr hy), hxy, ?_⟩
          intro z hz hxz
          rw [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact (lt_asymm hax hxz).elim
          · exact hmin z hz hxz
        · rintro ⟨hy, hxy, hmin⟩
          rw [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact (lt_asymm hax hxy).elim
          · refine ⟨hy, hxy, ?_⟩
            intro z hz hxz
            exact hmin z (List.mem_cons.mpr (Or.inr hz)) hxz

private theorem succSome_of_notmem {α : Type u} [LinearOrder α] {x y : α} {xs : List α}
    (hxs : List.Pairwise (· < ·) xs) (hx : x ∉ xs) :
    xs[((xs.filter (· < x)).length)]? = some y ↔
      y ∈ xs ∧ x < y ∧ ∀ z ∈ xs, x < z → y ≤ z := by
  induction xs with
  | nil =>
      have hnil : (([] : List α).filter (· < x)).length = 0 := by simp
      simp only [hnil]
      have hget : ([] : List α)[0]? = none := rfl
      rw [hget]
      constructor
      · intro h
        simp at h
      · rintro ⟨hy, -, -⟩
        simp at hy
  | cons a as ih =>
      rw [List.pairwise_cons] at hxs
      rcases hxs with ⟨ha, has⟩
      have hxne : x ≠ a := fun h => hx (by simp [h])
      have hxas : x ∉ as := fun h => hx (by simp [h])
      rcases lt_trichotomy a x with hax | hax | hax
      · -- The head is below the queried key: strip it.
        have hlen : (((a :: as).filter (· < x)).length)
            = ((as.filter (· < x)).length) + 1 := by simp [hax]
        simp only [hlen, List.getElem?_cons_succ, ih has hxas]
        constructor
        · rintro ⟨hy, hxy, hmin⟩
          refine ⟨List.mem_cons.mpr (Or.inr hy), hxy, ?_⟩
          intro z hz hxz
          rw [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact (lt_asymm hax hxz).elim
          · exact hmin z hz hxz
        · rintro ⟨hy, hxy, hmin⟩
          rw [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact (lt_asymm hax hxy).elim
          · refine ⟨hy, hxy, ?_⟩
            intro z hz hxz
            exact hmin z (List.mem_cons.mpr (Or.inr hz)) hxz
      · -- The head equals the queried key: impossible.
        exact (hxne hax.symm).elim
      · -- The head is above the queried key: it is the successor.
        have hall : ∀ b ∈ as, x < b := fun b hb => lt_trans hax (ha b hb)
        have hflt : (a :: as).filter (· < x) = [] := by
          have h1 : ¬ a < x := not_lt_of_gt hax
          have h2 : (a :: as).filter (· < x) = as.filter (· < x) := by simp [h1]
          rw [h2]
          exact filter_lt_nil_of_forall_gt hall
        have hlen : (((a :: as).filter (· < x)).length) = 0 := by simp [hflt]
        simp only [hlen, List.getElem?_cons_zero]
        constructor
        · intro h
          have hay : a = y := by simpa using h
          subst hay
          refine ⟨by simp, hax, ?_⟩
          intro z hz hxz
          rw [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact le_rfl
          · exact le_of_lt (ha z hz)
        · rintro ⟨hy, hxy, hmin⟩
          rw [List.mem_cons] at hy
          rcases hy with rfl | hy
          · rfl
          · have hya : y ≤ a := hmin a (by simp) hax
            have hay : a < y := ha y hy
            have hy' : y = a := le_antisymm hya (le_of_lt hay)
            simp [hy']

private theorem succNone_of_mem {α : Type u} [LinearOrder α] {x : α} {xs : List α}
    (hxs : List.Pairwise (· < ·) xs) (hx : x ∈ xs) :
    xs[((xs.filter (· < x)).length) + 1]? = none ↔ ∀ y ∈ xs, y ≤ x := by
  induction xs with
  | nil => simp at hx
  | cons a as ih =>
      rw [List.pairwise_cons] at hxs
      rcases hxs with ⟨ha, has⟩
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · -- The queried key is the head.
        have hflt : (x :: as).filter (· < x) = [] := by
          have h1 : ¬ x < x := lt_irrefl x
          have h2 : (x :: as).filter (· < x) = as.filter (· < x) := by simp [h1]
          rw [h2]
          exact filter_lt_nil_of_forall_gt ha
        have hlen : (((x :: as).filter (· < x)).length) = 0 := by simp [hflt]
        rw [hlen]
        clear ih
        revert ha has
        cases as with
        | nil =>
            intro has ha
            have hnil : (x :: ([] : List α))[0 + 1]? = none := rfl
            rw [hnil]
            constructor
            · intro _ y hy
              rw [List.mem_cons] at hy
              simp at hy
              rw [hy]
            · intro _
              rfl
        | cons b bs =>
            intro has ha
            have hcons : (x :: b :: bs)[0 + 1]? = some b := rfl
            rw [hcons]
            constructor
            · intro h
              simp at h
            · intro hmin
              have hab : x < b := ha b (by simp)
              have hba : b ≤ x := hmin b (by simp)
              exact absurd hba (not_le_of_gt hab)
      · -- The queried key is in the tail: strip the head.
        have hax : a < x := ha x hx
        have hlen : (((a :: as).filter (· < x)).length)
            = ((as.filter (· < x)).length) + 1 := by simp [hax]
        simp only [hlen, List.getElem?_cons_succ, ih has hx]
        constructor
        · intro hmin y hy
          rw [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact le_of_lt hax
          · exact hmin y hy
        · intro hmin y hy
          exact hmin y (List.mem_cons.mpr (Or.inr hy))

private theorem succNone_of_notmem {α : Type u} [LinearOrder α] {x : α} {xs : List α}
    (hxs : List.Pairwise (· < ·) xs) (hx : x ∉ xs) :
    xs[((xs.filter (· < x)).length)]? = none ↔ ∀ y ∈ xs, y ≤ x := by
  induction xs with
  | nil =>
      have hnil : (([] : List α).filter (· < x)).length = 0 := by simp
      simp only [hnil]
      have hget : ([] : List α)[0]? = none := rfl
      rw [hget]
      constructor
      · intro _ y hy
        simp at hy
      · intro _
        rfl
  | cons a as ih =>
      rw [List.pairwise_cons] at hxs
      rcases hxs with ⟨ha, has⟩
      have hxne : x ≠ a := fun h => hx (by simp [h])
      have hxas : x ∉ as := fun h => hx (by simp [h])
      rcases lt_trichotomy a x with hax | hax | hax
      · -- The head is below the queried key: strip it.
        have hlen : (((a :: as).filter (· < x)).length)
            = ((as.filter (· < x)).length) + 1 := by simp [hax]
        simp only [hlen, List.getElem?_cons_succ, ih has hxas]
        constructor
        · intro hmin y hy
          rw [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact le_of_lt hax
          · exact hmin y hy
        · intro hmin y hy
          exact hmin y (List.mem_cons.mpr (Or.inr hy))
      · exact (hxne hax.symm).elim
      · -- The head is above the queried key: a successor exists.
        have hall : ∀ b ∈ as, x < b := fun b hb => lt_trans hax (ha b hb)
        have hflt : (a :: as).filter (· < x) = [] := by
          have h1 : ¬ a < x := not_lt_of_gt hax
          have h2 : (a :: as).filter (· < x) = as.filter (· < x) := by simp [h1]
          rw [h2]
          exact filter_lt_nil_of_forall_gt hall
        have hlen : (((a :: as).filter (· < x)).length) = 0 := by simp [hflt]
        simp only [hlen, List.getElem?_cons_zero]
        constructor
        · intro h
          simp at h
        · intro hmin
          have hax' : a ≤ x := hmin a (by simp)
          exact absurd hax' (not_le_of_gt hax)

public theorem successor_eq_some_iff {α : Type u} [LinearOrder α] {x y : α}
    {tree : BinaryTree α} (hTree : Ordered tree) :
    successor x tree = some y ↔
      y ∈ tree ∧ x < y ∧ ∀ z ∈ tree, x < z → y ≤ z := by
  have hord := ordered_inorder hTree
  by_cases hx : x ∈ tree
  · have hsucc : successor x tree = select tree (rank x tree + 1) := by
      simp [successor, hx]
    rw [hsucc, select_eq_getElem?_inorder, rank_eq_count_inorder,
      succSome_of_mem hord (mem_inorder.mpr hx)]
    constructor
    · rintro ⟨hy, hxy, hmin⟩
      refine ⟨mem_inorder.mp hy, hxy, ?_⟩
      intro z hz hxz
      exact hmin z (mem_inorder.mpr hz) hxz
    · rintro ⟨hy, hxy, hmin⟩
      refine ⟨mem_inorder.mpr hy, hxy, ?_⟩
      intro z hz hxz
      exact hmin z (mem_inorder.mp hz) hxz
  · have hsucc : successor x tree = select tree (rank x tree) := by
      simp [successor, hx]
    rw [hsucc, select_eq_getElem?_inorder, rank_eq_count_inorder,
      succSome_of_notmem hord (mt mem_inorder.mp hx)]
    constructor
    · rintro ⟨hy, hxy, hmin⟩
      refine ⟨mem_inorder.mp hy, hxy, ?_⟩
      intro z hz hxz
      exact hmin z (mem_inorder.mpr hz) hxz
    · rintro ⟨hy, hxy, hmin⟩
      refine ⟨mem_inorder.mpr hy, hxy, ?_⟩
      intro z hz hxz
      exact hmin z (mem_inorder.mp hz) hxz

public theorem successor_eq_none_iff {α : Type u} [LinearOrder α] {x : α}
    {tree : BinaryTree α} (hTree : Ordered tree) :
    successor x tree = none ↔ ∀ y ∈ tree, y ≤ x := by
  have hord := ordered_inorder hTree
  by_cases hx : x ∈ tree
  · have hsucc : successor x tree = select tree (rank x tree + 1) := by
      simp [successor, hx]
    rw [hsucc, select_eq_getElem?_inorder, rank_eq_count_inorder,
      succNone_of_mem hord (mem_inorder.mpr hx)]
    constructor
    · intro hmin y hy
      exact hmin y (mem_inorder.mpr hy)
    · intro hmin y hy
      exact hmin y (mem_inorder.mp hy)
  · have hsucc : successor x tree = select tree (rank x tree) := by
      simp [successor, hx]
    rw [hsucc, select_eq_getElem?_inorder, rank_eq_count_inorder,
      succNone_of_notmem hord (mt mem_inorder.mp hx)]
    constructor
    · intro hmin y hy
      exact hmin y (mem_inorder.mpr hy)
    · intro hmin y hy
      exact hmin y (mem_inorder.mp hy)

/-- **Predecessor in a binary search tree.** For a linearly ordered type `α`, a
key `x` and a binary tree `t`, the predecessor of `x` in `t` is the last entry
of the inorder traversal of `t` that is strictly less than `x`; equivalently
the greatest key of `t` strictly smaller than `x` on ordered trees. This is a
traversal specification; it claims no navigation cost. -/
public def predecessor {α : Type u} [LinearOrder α] (x : α) (tree : BinaryTree α) :
    Option α :=
  if h : 0 < rank x tree then select tree (rank x tree - 1) else none

private theorem le_of_filter_length_eq_zero {α : Type u} [LinearOrder α] {x : α}
    {xs : List α} (h : ((xs.filter (· < x)).length) = 0) {z : α} (hz : z ∈ xs) :
    x ≤ z := by
  have hnil : xs.filter (· < x) = [] := List.eq_nil_of_length_eq_zero h
  have hall := (List.filter_eq_nil_iff.mp hnil) z hz
  simp only [decide_eq_true_eq] at hall
  exact le_of_not_gt hall

private theorem predSome_of_pos {α : Type u} [LinearOrder α] {x y : α} {xs : List α}
    (hxs : List.Pairwise (· < ·) xs) (hpos : 0 < ((xs.filter (· < x)).length)) :
    xs[((xs.filter (· < x)).length) - 1]? = some y ↔
      y ∈ xs ∧ y < x ∧ ∀ z ∈ xs, z < x → z ≤ y := by
  induction xs with
  | nil =>
      simp at hpos
  | cons a as ih =>
      rw [List.pairwise_cons] at hxs
      rcases hxs with ⟨ha, has⟩
      rcases lt_trichotomy a x with hax | hax | hax
      · -- The head is below the queried key: it is the predecessor unless the tail
        -- holds a smaller key that is still below the queried key.
        have hlen : (((a :: as).filter (· < x)).length)
            = ((as.filter (· < x)).length) + 1 := by simp [hax]
        rw [hlen, Nat.add_sub_cancel]
        by_cases hj : (as.filter (· < x)).length = 0
        · -- No smaller key in the tail is below the queried key: the head is the
          -- predecessor.
          rw [hj]
          simp only [List.getElem?_cons_zero]
          constructor
          · intro h
            have hay : a = y := by simpa using h
            subst hay
            refine ⟨by simp, hax, ?_⟩
            intro z hz hzx
            rw [List.mem_cons] at hz
            rcases hz with rfl | hz
            · exact le_rfl
            · exact (not_le_of_gt hzx (le_of_filter_length_eq_zero hj hz)).elim
          · rintro ⟨hy, hyx, hmax⟩
            rw [List.mem_cons] at hy
            rcases hy with rfl | hy
            · rfl
            · exact (not_le_of_gt hyx (le_of_filter_length_eq_zero hj hy)).elim
        · -- The tail holds a smaller key below the queried key: recurse into it.
          have hpos' : 0 < (as.filter (· < x)).length := Nat.pos_of_ne_zero hj
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj
          have hk' : (as.filter (· < x)).length = k + 1 := by omega
          rw [hk', List.getElem?_cons_succ]
          have hIH := ih has hpos'
          rw [hk'] at hIH
          simp only [Nat.add_sub_cancel] at hIH
          rw [hIH]
          constructor
          · rintro ⟨hy, hyx, hmax⟩
            refine ⟨List.mem_cons.mpr (Or.inr hy), hyx, ?_⟩
            intro z hz hzx
            rw [List.mem_cons] at hz
            rcases hz with rfl | hz
            · exact le_of_lt (ha y hy)
            · exact hmax z hz hzx
          · rintro ⟨hy, hyx, hmax⟩
            rw [List.mem_cons] at hy
            rcases hy with hya | hy
            · -- The head cannot be maximal: the tail holds a key below `x`
              -- which exceeds the head.
              have hne : (as.filter (· < x)) ≠ [] := by
                intro hnil
                simp [hnil] at hpos'
              obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
              rw [List.mem_filter] at hw
              simp only [decide_eq_true_eq] at hw
              have hwa : w ≤ y :=
                hmax w (List.mem_cons.mpr (Or.inr hw.1)) hw.2
              have hwa' : w ≤ a := by
                rw [hya] at hwa
                exact hwa
              exact (lt_irrefl a (lt_of_lt_of_le (ha w hw.1) hwa')).elim
            · refine ⟨hy, hyx, ?_⟩
              intro z hz hzx
              exact hmax z (List.mem_cons.mpr (Or.inr hz)) hzx
      · -- The head equals the queried key: it is the minimum, so no smaller key
        -- exists.
        have h1 : ¬ a < x := by
          rw [hax]
          exact lt_irrefl x
        have hflt : (a :: as).filter (· < x) = as.filter (· < x) := by simp [h1]
        have hall : ∀ b ∈ as, x < b := by
          intro b hb
          rw [← hax]
          exact ha b hb
        have hnil : as.filter (· < x) = [] := filter_lt_nil_of_forall_gt hall
        have hlen0 : (((a :: as).filter (· < x)).length) = 0 := by simp [hflt, hnil]
        omega
      · -- The head is above the queried key: no smaller key exists.
        have hall : ∀ b ∈ a :: as, x < b := by
          intro b hb
          rw [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact hax
          · exact lt_trans hax (ha b hb)
        have hnil : (a :: as).filter (· < x) = [] :=
          filter_lt_nil_of_forall_gt hall
        have hlen0 : (((a :: as).filter (· < x)).length) = 0 := by simp [hnil]
        omega

private theorem predNone_of_pos {α : Type u} [LinearOrder α] {x : α} {xs : List α}
    (hxs : List.Pairwise (· < ·) xs) (hpos : 0 < ((xs.filter (· < x)).length)) :
    xs[((xs.filter (· < x)).length) - 1]? = none ↔ ∀ y ∈ xs, x ≤ y := by
  have hlt : ((xs.filter (· < x)).length) - 1 < xs.length := by
    have hle := List.length_filter_le (· < x) xs
    omega
  have hsome := List.getElem?_eq_getElem hlt
  have hw := (predSome_of_pos hxs hpos).mp hsome
  rcases hw with ⟨hmem, hwlt, -⟩
  constructor
  · intro hnone
    rw [hsome] at hnone
    simp at hnone
  · intro hall
    exact absurd (hall _ hmem) (not_le_of_gt hwlt)

public theorem predecessor_eq_some_iff {α : Type u} [LinearOrder α] {x y : α}
    {tree : BinaryTree α} (hTree : Ordered tree) :
    predecessor x tree = some y ↔
      y ∈ tree ∧ y < x ∧ ∀ z ∈ tree, z < x → z ≤ y := by
  have hord := ordered_inorder hTree
  by_cases hpos : 0 < rank x tree
  · have hpred : predecessor x tree = select tree (rank x tree - 1) := by
      simp [predecessor, hpos]
    have hpos' : 0 < (((inorder tree).filter (· < x)).length) := by
      rw [← rank_eq_count_inorder]
      exact hpos
    rw [hpred, select_eq_getElem?_inorder, rank_eq_count_inorder,
      predSome_of_pos hord hpos']
    constructor
    · rintro ⟨hy, hyx, hmax⟩
      refine ⟨mem_inorder.mp hy, hyx, ?_⟩
      intro z hz hzx
      exact hmax z (mem_inorder.mpr hz) hzx
    · rintro ⟨hy, hyx, hmax⟩
      refine ⟨mem_inorder.mpr hy, hyx, ?_⟩
      intro z hz hzx
      exact hmax z (mem_inorder.mp hz) hzx
  · have hpred : predecessor x tree = none := by
      simp [predecessor, hpos]
    have hzero : (((inorder tree).filter (· < x)).length) = 0 := by
      rw [← rank_eq_count_inorder]
      omega
    rw [hpred]
    constructor
    · intro h
      simp at h
    · rintro ⟨hy, hyx, -⟩
      exact absurd (le_of_filter_length_eq_zero hzero (mem_inorder.mpr hy))
        (not_le_of_gt hyx)

public theorem predecessor_eq_none_iff {α : Type u} [LinearOrder α] {x : α}
    {tree : BinaryTree α} (hTree : Ordered tree) :
    predecessor x tree = none ↔ ∀ y ∈ tree, x ≤ y := by
  have hord := ordered_inorder hTree
  by_cases hpos : 0 < rank x tree
  · have hpred : predecessor x tree = select tree (rank x tree - 1) := by
      simp [predecessor, hpos]
    have hpos' : 0 < (((inorder tree).filter (· < x)).length) := by
      rw [← rank_eq_count_inorder]
      exact hpos
    rw [hpred, select_eq_getElem?_inorder, rank_eq_count_inorder,
      predNone_of_pos hord hpos']
    constructor
    · intro hall y hy
      exact hall y (mem_inorder.mpr hy)
    · intro hall y hy
      exact hall y (mem_inorder.mp hy)
  · have hpred : predecessor x tree = none := by
      simp [predecessor, hpos]
    have hzero : (((inorder tree).filter (· < x)).length) = 0 := by
      rw [← rank_eq_count_inorder]
      omega
    rw [hpred]
    constructor
    · intro _ y hy
      exact le_of_filter_length_eq_zero hzero (mem_inorder.mpr hy)
    · intro _
      rfl

end BinarySearchTree
end Cslib.Algorithms.Lean
end
