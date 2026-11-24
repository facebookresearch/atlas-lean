/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinarySearchTree

/-!
# Successor queries in binary search trees

The successor of a key `x` is the least stored key strictly greater than `x`, and `none`
exactly when no stored key exceeds `x`. Like `rank` and `select`, `successor` is a
traversal specification via the inorder traversal; it claims no navigation cost.
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

end BinarySearchTree
end Cslib.Algorithms.Lean
end
