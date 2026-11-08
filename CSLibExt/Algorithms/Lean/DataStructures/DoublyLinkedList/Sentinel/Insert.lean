/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Sentinel.Basic
import CSLibExt.Algorithms.Lean.DataStructures.DoublyLinkedList.Insert
import Mathlib.Data.List.Basic

/-!
# Sentinel insertion, CLRS4 section10.2 printed263

Exactly four carried-store assignments, one tick per actual write.
Access-valid aliases are allowed; freshness is a correctness premise only.
Private carried-store proof facts are adapted from landed U056 Insert.lean.
Its existing public field theorems will be reused only after actual-return equality.
No NIL test, allocation, head update, RAM/bit/space or native-time claim.
-/

set_option autoImplicit false
namespace Cslib.Algorithms.Lean.DoublyLinkedList
open Cslib.Algorithms.Lean
universe u

private lemma get_set {α : Type u} {n : Nat} (s : Vector α n)
    (i j : Fin n) (value : α) :
    (s.set i.val value i.isLt).get j = if i = j then value else s.get j := by
  change (s.set i.val value i.isLt)[j.val] = if i = j then value else s[j.val]
  rw [Vector.getElem_set]
  simp only [Fin.ext_iff]

private lemma allocated_set {α : Type u} {n : Nat} (s : Vector (Option α) n)
    (i : Fin n) (h : (s.get i).isSome) (value : α) (j : Fin n) :
    ((s.set i.val (some value) i.isLt).get j).isSome = (s.get j).isSome := by
  rw [get_set]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, Option.isSome_some]
    exact h.symm
  · simp only [hij, ite_false]

private lemma y_next_after_set {α : Type u} {n : Nat}
    (s : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (s.get x).isSome) (hy : (s.get y).isSome) :
    let value := { (s.get x).get hx with next := ((s.get y).get hy).next }
    let updated := s.set x.val (some value) x.isLt
    ((updated.get y).get ((allocated_set s x hx value y).trans hy)).next =
      ((s.get y).get hy).next := by
  dsimp only
  by_cases hxy : x = y
  · subst y
    simp only [get_set, ite_true, Option.get_some]
  · simp only [get_set, hxy, ite_false]

private lemma y_next_after_prev {α : Type u} {n : Nat}
    (s : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (s.get x).isSome) (hy : (s.get y).isSome) :
    let value := { (s.get x).get hx with prev := some y }
    let updated := s.set x.val (some value) x.isLt
    ((updated.get y).get ((allocated_set s x hx value y).trans hy)).next =
      ((s.get y).get hy).next := by
  dsimp only
  by_cases hxy : x = y
  · subst y
    simp only [get_set, ite_true, Option.get_some]
  · simp only [get_set, hxy, ite_false]

/-- The four assignments of LIST-INSERT-prime, without a NIL branch. -/
public def sentinelInsert {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ z, ((store.get y).get hy).next = some z → (store.get z).isSome) :
    TimeM Nat (Vector (Option (Node α (Fin n))) n) := do
  let oldY := (store.get y).get hy
  TimeM.tick 1
  let nextX := { (store.get x).get hx with next := oldY.next }
  let store1 := store.set x.val (some nextX) x.isLt
  have hx1 := (allocated_set store x hx nextX x).trans hx
  have hy1 := (allocated_set store x hx nextX y).trans hy
  TimeM.tick 1
  let prevX := { (store1.get x).get hx1 with prev := some y }
  let store2 := store1.set x.val (some prevX) x.isLt
  have hy2 := (allocated_set store1 x hx1 prevX y).trans hy1
  let currentY2 := (store2.get y).get hy2
  have nextPreserved : currentY2.next = oldY.next :=
    (y_next_after_prev store1 x y hx1 hy1).trans
      (y_next_after_set store x y hx hy)
  have hn2 : currentY2.next.isSome := by rw [nextPreserved]; exact hn
  let z := currentY2.next.get hn2
  have he : oldY.next = some z :=
    nextPreserved.symm.trans (Option.some_get hn2).symm
  have hz := hs z he
  have hz1 := (allocated_set store x hx nextX z).trans hz
  have hz2 := (allocated_set store1 x hx1 prevX z).trans hz1
  TimeM.tick 1
  let newZ := { (store2.get z).get hz2 with prev := some x }
  let store3 := store2.set z.val (some newZ) z.isLt
  have hy3 := (allocated_set store2 z hz2 newZ y).trans hy2
  TimeM.tick 1
  pure (store3.set y.val
    (some { (store3.get y).get hy3 with next := some x }) y.isLt)

private lemma set_map_get {α : Type u} {n : Nat} (s : Vector (Option α) n)
    (i : Fin n) (h : (s.get i).isSome) (f : α → α) :
    s.set i.val (some (f ((s.get i).get h))) i.isLt =
      s.set i.val ((s.get i).map f) i.isLt := by
  exact congrArg (fun value => s.set i.val value i.isLt)
    (congrArg (Option.map f) (Option.some_get h))

private lemma first_two_store {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome) :
    let nextX := { (store.get x).get hx with next := ((store.get y).get hy).next }
    let store1 := store.set x.val (some nextX) x.isLt
    let hx1 := (allocated_set store x hx nextX x).trans hx
    store1.set x.val (some { (store1.get x).get hx1 with prev := some y }) x.isLt =
      store.set x.val
        (some { (store.get x).get hx with
          next := ((store.get y).get hy).next, prev := some y }) x.isLt := by
  dsimp only
  simp only [get_set, ite_true, Option.get_some, Vector.set_set]

@[expose] public section

/-- Same-run logical pointer assignments, not full RAM cost. -/
public theorem sentinelInsert_time {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ z, ((store.get y).get hy).next = some z → (store.get z).isSome) :
    (sentinelInsert store x y hx hy hn hs).time = 4 := by
  simp [sentinelInsert, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]

/-- Complete carried-store characteristic, without freshness. -/
public theorem sentinelInsert_ret {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ z, ((store.get y).get hy).next = some z → (store.get z).isSome) :
    let updated := store.set x.val (some { (store.get x).get hx with
      next := ((store.get y).get hy).next, prev := some y }) x.isLt
    let z := ((store.get y).get hy).next.get hn
    let backlinked := updated.set z.val
      ((updated.get z).map fun (node : Node α (Fin n)) =>
        { node with prev := some x }) z.isLt
    (sentinelInsert store x y hx hy hn hs).ret = backlinked.set y.val
      ((backlinked.get y).map fun (node : Node α (Fin n)) =>
        { node with next := some x }) y.isLt := by
  let oldY := (store.get y).get hy
  let nextX := { (store.get x).get hx with next := oldY.next }
  let store1 := store.set x.val (some nextX) x.isLt
  have hx1 := (allocated_set store x hx nextX x).trans hx
  have hy1 := (allocated_set store x hx nextX y).trans hy
  let prevX := { (store1.get x).get hx1 with prev := some y }
  let store2 := store1.set x.val (some prevX) x.isLt
  have hy2 := (allocated_set store1 x hx1 prevX y).trans hy1
  let currentY2 := (store2.get y).get hy2
  have hp : currentY2.next = oldY.next :=
    (y_next_after_prev store1 x y hx1 hy1).trans (y_next_after_set store x y hx hy)
  have hn2 : currentY2.next.isSome := by rw [hp]; exact hn
  let z := oldY.next.get hn
  have hOld : oldY.next = some z := (Option.some_get hn).symm
  have hzEq : currentY2.next.get hn2 = z := by
    apply Option.some.inj
    exact (Option.some_get hn2).trans (hp.trans hOld)
  have hz := hs z hOld
  have hz1 := (allocated_set store x hx nextX z).trans hz
  have hz2 := (allocated_set store1 x hx1 prevX z).trans hz1
  let newZ := { (store2.get z).get hz2 with prev := some x }
  let store3 := store2.set z.val (some newZ) z.isLt
  have hy3 := (allocated_set store2 z hz2 newZ y).trans hy2
  let updated := store.set x.val (some { (store.get x).get hx with
    next := oldY.next, prev := some y }) x.isLt
  have hS2 : store2 = updated := first_two_store store x y hx hy
  let backlinked := updated.set z.val
    ((updated.get z).map fun (node : Node α (Fin n)) => { node with prev := some x })
    z.isLt
  have hS3 : store3 = backlinked := by
    calc
      _ = store2.set z.val ((store2.get z).map fun (node : Node α (Fin n)) =>
          { node with prev := some x }) z.isLt :=
        set_map_get store2 z hz2 (fun node => { node with prev := some x })
      _ = _ := by rw [hS2]
  change (sentinelInsert store x y hx hy hn hs).ret = backlinked.set y.val
    ((backlinked.get y).map fun (node : Node α (Fin n)) => { node with next := some x })
    y.isLt
  simp only [sentinelInsert, TimeM.ret_bind, TimeM.ret_pure]
  change
    (store2.set (currentY2.next.get hn2).val
      (some { (store2.get (currentY2.next.get hn2)).get _ with prev := some x })
      (currentY2.next.get hn2).isLt).set y.val
      (some { ((store2.set (currentY2.next.get hn2).val
        (some { (store2.get (currentY2.next.get hn2)).get _ with prev := some x })
        (currentY2.next.get hn2).isLt).get y).get _ with next := some x }) y.isLt = _
  simp only [hzEq]
  change store3.set y.val (some { (store3.get y).get hy3 with next := some x }) y.isLt = _
  calc
    _ = store3.set y.val ((store3.get y).map fun (node : Node α (Fin n)) =>
        { node with next := some x }) y.isLt :=
      set_map_get store3 y hy3 (fun node => { node with next := some x })
    _ = _ := by rw [hS3]

private lemma ret_eq_listInsert {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ z, ((store.get y).get hy).next = some z → (store.get z).isSome) :
    (sentinelInsert store x y hx hy hn hs).ret = (listInsert store x y hx hy hs).ret := by
  rw [sentinelInsert_ret, listInsert_ret]
  let z := ((store.get y).get hy).next.get hn
  have he : ((store.get y).get hy).next = some z := (Option.some_get hn).symm
  simp only [he, Option.get_some]

/-- The source-ordered update at every cell, including aliased write targets. -/
public theorem sentinelInsert_get {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y z : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ w, ((store.get y).get hy).next = some w → (store.get w).isSome) :
    let first := if x = z then some { (store.get x).get hx with
      next := ((store.get y).get hy).next, prev := some y } else store.get z
    let second := if ((store.get y).get hy).next = some z then
      first.map (fun (node : Node α (Fin n)) => { node with prev := some x }) else first
    (sentinelInsert store x y hx hy hn hs).ret.get z =
      if y = z then second.map (fun (node : Node α (Fin n)) =>
        { node with next := some x }) else second := by
  simp only [ret_eq_listInsert]
  exact listInsert_get store x y z hx hy hs

/-- Cells outside the inserted node, predecessor and old successor are unchanged. -/
public theorem sentinelInsert_frame {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y z : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ w, ((store.get y).get hy).next = some w → (store.get w).isSome)
    (hxz : x ≠ z) (hyz : y ≠ z) (hsz : ((store.get y).get hy).next ≠ some z) :
    (sentinelInsert store x y hx hy hn hs).ret.get z = store.get z := by
  simp only [ret_eq_listInsert]
  exact listInsert_frame store x y z hx hy hs hxz hyz hsz

/-- Insertion neither allocates nor deallocates a cell, even with aliased targets. -/
public theorem sentinelInsert_allocated {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y z : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ w, ((store.get y).get hy).next = some w → (store.get w).isSome) :
    ((sentinelInsert store x y hx hy hn hs).ret.get z).isSome =
      (store.get z).isSome := by
  simp only [ret_eq_listInsert]
  exact listInsert_allocated store x y z hx hy hs

/-- Every payload, including keys and satellite data, is preserved. -/
public theorem sentinelInsert_payload {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y z : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ w, ((store.get y).get hy).next = some w → (store.get w).isSome) :
    ((sentinelInsert store x y hx hy hn hs).ret.get z).map Node.payload =
      (store.get z).map Node.payload := by
  simp only [ret_eq_listInsert]
  exact listInsert_payload store x y z hx hy hs

private lemma lastD_fallback {α : Type u} (l : List α) (h : l ≠ []) (a b : α) :
    l.getLastD a = l.getLastD b := by
  cases l with
  | nil => exact False.elim (h rfl)
  | cons x xs => simp only [List.getLastD_cons]

private lemma lastD_append {α : Type u} (l r : List α) (s : α) (hr : r ≠ []) :
    (l ++ r).getLastD s = r.getLastD s := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    rw [List.cons_append, List.getLastD_cons, ih]
    exact lastD_fallback r hr a s

private lemma headD_append {α : Type u} (l r : List α) (s : α) (hl : l ≠ []) :
    (l ++ r).headD s = l.headD s := by
  cases l with
  | nil => exact False.elim (hl rfl)
  | cons x xs => rfl

private lemma circular_next_boundary {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (s : Fin n)
    (before after : List (Fin n))
    (hc : CircularRepresents store s (before ++ after)) :
    ∃ node, store.get (before.getLastD s) = some node ∧
      node.next = some (after.headD s) := by
  rcases List.eq_nil_or_concat' before with h | ⟨l, a, h⟩
  · subst before
    obtain ⟨node, hn, hnext, _⟩ := hc.2.2.1
    exact ⟨node, hn, hnext⟩
  · rw [h, List.getLastD_concat]
    obtain ⟨node, hn, _, hnext⟩ := hc.2.2.2 l a after
      (by rw [h]; simp only [List.append_assoc, List.singleton_append])
    exact ⟨node, hn, hnext⟩


private lemma headD_mem {α : Type u} (l : List α) (s : α) (h : l ≠ []) :
    l.headD s ∈ l := by
  cases l with
  | nil => exact False.elim (h rfl)
  | cons a l => exact List.mem_cons_self

private lemma lastD_mem {α : Type u} (l : List α) (s : α) (h : l ≠ []) :
    l.getLastD s ∈ l := by
  cases l with
  | nil => exact False.elim (h rfl)
  | cons a l => simpa only [List.getLastD_cons] using (@List.getLastD_mem_cons α l a)

private lemma headD_eq_default {α : Type u} (l : List α) (s : α) (h : s ∉ l) :
    l.headD s = s ↔ l = [] := by
  constructor
  · intro he
    by_contra hl
    exact h (he ▸ headD_mem l s hl)
  · rintro rfl; rfl

private lemma lastD_eq_default {α : Type u} (l : List α) (s : α) (h : s ∉ l) :
    l.getLastD s = s ↔ l = [] := by
  constructor
  · intro he
    by_contra hl
    exact h (he ▸ lastD_mem l s hl)
  · rintro rfl; rfl

private lemma existing_get {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y a : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ z, ((store.get y).get hy).next = some z → (store.get z).isSome)
    (node : Node α (Fin n)) (ha : store.get a = some node) (hxa : x ≠ a) :
    (sentinelInsert store x y hx hy hn hs).ret.get a =
      some { node with
        prev := if ((store.get y).get hy).next = some a then some x else node.prev
        next := if y = a then some x else node.next } := by
  rw [sentinelInsert_get]
  by_cases hya : y = a
  · subst y
    by_cases hp : node.next = some a <;> simp [hxa, ha, hp]
  · by_cases hp : ((store.get y).get hy).next = some a <;>
      simp [hxa, ha, hp, hya]

private lemma new_get {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y : Fin n)
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ z, ((store.get y).get hy).next = some z → (store.get z).isSome)
    (hxy : x ≠ y) (hsx : ((store.get y).get hy).next ≠ some x) :
    (sentinelInsert store x y hx hy hn hs).ret.get x =
      some { (store.get x).get hx with
        next := ((store.get y).get hy).next, prev := some y } := by
  rw [sentinelInsert_get]
  simp [hxy.symm, hsx]

private lemma insert_split_cases {α : Type u} (before after left right : List α)
    (x a : α) (h : before ++ x :: after = left ++ a :: right) :
    (a = x ∧ left = before ∧ right = after) ∨
      (∃ middle, before = left ++ a :: middle ∧ right = middle ++ x :: after) ∨
      (∃ middle, left = before ++ x :: middle ∧ after = middle ++ a :: right) := by
  rcases List.append_eq_append_iff.mp h with ⟨m, hl, hr⟩ | ⟨m, hl, hr⟩
  · cases m with
    | nil =>
      simp only [List.append_nil] at hl
      simp only [List.nil_append, List.cons.injEq] at hr
      exact Or.inl ⟨hr.1.symm, hl, hr.2.symm⟩
    | cons b middle =>
      simp only [List.cons_append, List.cons.injEq] at hr
      obtain ⟨rfl, hr⟩ := hr
      exact Or.inr (Or.inr ⟨middle, hl, hr⟩)
  · cases m with
    | nil =>
      simp only [List.append_nil] at hl
      simp only [List.nil_append, List.cons.injEq] at hr
      exact Or.inl ⟨hr.1, hl.symm, hr.2⟩
    | cons b middle =>
      simp only [List.cons_append, List.cons.injEq] at hr
      obtain ⟨rfl, hr⟩ := hr
      exact Or.inr (Or.inl ⟨middle, hl, hr⟩)


private lemma headD_ne {α : Type u} (l : List α) (s a : α)
    (hs : s ≠ a) (ha : a ∉ l) : l.headD s ≠ a := by
  by_cases hl : l = []
  · simpa only [hl, List.headD_nil] using hs
  · intro he
    exact ha (he ▸ headD_mem l s hl)

private lemma lastD_ne {α : Type u} (l : List α) (s a : α)
    (hs : s ≠ a) (ha : a ∉ l) : l.getLastD s ≠ a := by
  by_cases hl : l = []
  · simpa only [hl, List.getLastD_nil] using hs
  · intro he
    exact ha (he ▸ lastD_mem l s hl)

private lemma nodup_insert_split {α : Type u} (before after : List α) (x : α)
    (h : (before ++ after).Nodup) (hx : x ∉ before ++ after) :
    (before ++ x :: after).Nodup := by
  rw [List.nodup_append] at h ⊢
  simp only [List.mem_append, not_or] at hx
  refine ⟨h.1, List.nodup_cons.mpr ⟨hx.2, h.2.1⟩, ?_⟩
  intro a ha b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · intro he; exact hx.1 (he ▸ ha)
  · exact h.2.2 a ha b hb


/-- Inserting a fresh allocated identity preserves the exact circular list representation. -/
public theorem sentinelInsert_circular {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y s : Fin n)
    (ids before after : List (Fin n))
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ z, ((store.get y).get hy).next = some z → (store.get z).isSome)
    (hc : CircularRepresents store s ids)
    (hSplit : ids = before ++ after) (hPosition : y = before.getLastD s)
    (hFreshSentinel : x ≠ s) (hFreshData : x ∉ ids) :
    CircularRepresents (sentinelInsert store x y hx hy hn hs).ret s
      (before ++ x :: after) := by
  subst ids
  subst y
  have hxBefore : x ∉ before := fun h => hFreshData (List.mem_append_left after h)
  have hxAfter : x ∉ after := fun h => hFreshData (List.mem_append_right before h)
  have hsBefore : s ∉ before := fun h => hc.2.1 (List.mem_append_left after h)
  have hsAfter : s ∉ after := fun h => hc.2.1 (List.mem_append_right before h)
  obtain ⟨previous, hPrevious, hNext⟩ := circular_next_boundary store s before after hc
  have hPreviousGet : (store.get (before.getLastD s)).get hy = previous :=
    Option.some.inj ((Option.some_get hy).trans hPrevious)
  have hNextEq : ((store.get (before.getLastD s)).get hy).next =
      some (after.headD s) := by rw [hPreviousGet]; exact hNext
  refine ⟨nodup_insert_split before after x hc.1 hFreshData, ?_, ?_, ?_⟩
  · simp only [List.mem_append, List.mem_cons, not_or]
    exact ⟨hsBefore, hFreshSentinel.symm, hsAfter⟩
  · obtain ⟨node, hNode, hNodeNext, hNodePrev⟩ := hc.2.2.1
    have hg := existing_get store x (before.getLastD s) s hx hy hn hs node hNode
      hFreshSentinel
    rw [hNextEq] at hg
    refine ⟨_, hg, ?_, ?_⟩
    · change (if before.getLastD s = s then some x else node.next) =
        some ((before ++ x :: after).headD s)
      rw [hNodeNext]
      by_cases hb : before = []
      · subst before
        simp only [List.getLastD_nil, ite_true, List.nil_append, List.headD_cons]
      · have hbS : before.getLastD s ≠ s :=
          fun he => hb ((lastD_eq_default before s hsBefore).mp he)
        simp only [hbS, ite_false]
        rw [headD_append before after s hb, headD_append before (x :: after) s hb]
    · change (if some (after.headD s) = some s then some x else node.prev) =
        some ((before ++ x :: after).getLastD s)
      rw [hNodePrev]
      by_cases ha : after = []
      · subst after
        simp only [List.headD_nil, ite_true, List.getLastD_concat]
      · have haS : after.headD s ≠ s :=
          fun he => ha ((headD_eq_default after s hsAfter).mp he)
        simp only [Option.some.injEq, haS, ite_false]
        rw [lastD_append before after s ha,
          lastD_append before (x :: after) s (List.cons_ne_nil x after),
          List.getLastD_cons, lastD_fallback after ha x s]
  · intro left a right hCut
    rcases insert_split_cases before after left right x a hCut with
      ⟨hax, hleft, hright⟩ | ⟨middle, hBefore, hRight⟩ | ⟨middle, hLeft, hAfter⟩
    · subst a
      subst left
      subst right
      have hxy : x ≠ before.getLastD s :=
        (lastD_ne before s x hFreshSentinel.symm hxBefore).symm
      have hnx : ((store.get (before.getLastD s)).get hy).next ≠ some x := by
        rw [hNextEq]
        exact fun he => headD_ne after s x hFreshSentinel.symm hxAfter
          (Option.some.inj he)
      refine ⟨_, new_get store x (before.getLastD s) hx hy hn hs hxy hnx, rfl, hNextEq⟩
    · subst before
      subst right
      obtain ⟨node, hNode, hPrev, hSucc⟩ := hc.2.2.2 left a (middle ++ after)
        (by simp only [List.append_assoc, List.cons_append])
      have hxa : x ≠ a := by
        intro he; apply hFreshData; simp only [he, List.mem_append, List.mem_cons]; tauto
      have hsa : s ≠ a := by
        intro he; apply hc.2.1; simp only [he, List.mem_append, List.mem_cons]; tauto
      have haAfter : a ∉ after := by
        intro ha
        exact (List.disjoint_of_nodup_append hc.1)
          (by simp only [List.mem_append, List.mem_cons]; tauto) ha
      have hza := headD_ne after s a hsa haAfter
      have hg := existing_get store x ((left ++ a :: middle).getLastD s) a hx hy hn hs
        node hNode hxa
      rw [hNextEq] at hg
      refine ⟨_, hg, ?_, ?_⟩
      · change (if some (after.headD s) = some a then some x else node.prev) =
          some (left.getLastD s)
        simp only [Option.some.injEq, hza, ite_false, hPrev]
      · change (if (left ++ a :: middle).getLastD s = a then some x else node.next) =
          some ((middle ++ x :: after).headD s)
        by_cases hm : middle = []
        · subst middle
          simp only [List.getLastD_concat, ite_true, List.nil_append, List.headD_cons]
        · have haMiddle : a ∉ middle := by
            intro ha
            have hnd : (left ++ a :: (middle ++ after)).Nodup := by
              simpa only [List.append_assoc, List.cons_append] using hc.1
            exact (List.nodup_cons.mp hnd.of_append_right).1
              (List.mem_append_left after ha)
          have hya : (left ++ a :: middle).getLastD s ≠ a := by
            rw [lastD_append left (a :: middle) s (List.cons_ne_nil a middle),
              List.getLastD_cons, lastD_fallback middle hm a s]
            exact lastD_ne middle s a hsa haMiddle
          simp only [hya, ite_false, hSucc]
          rw [headD_append middle after s hm, headD_append middle (x :: after) s hm]
    · subst left
      subst after
      obtain ⟨node, hNode, hPrev, hSucc⟩ := hc.2.2.2 (before ++ middle) a right
        (by simp only [List.append_assoc])
      have hxa : x ≠ a := by
        intro he; apply hFreshData; simp only [he, List.mem_append, List.mem_cons]; tauto
      have hsa : s ≠ a := by
        intro he; apply hc.2.1; simp only [he, List.mem_append, List.mem_cons]; tauto
      have haBefore : a ∉ before := by
        intro ha
        exact (List.disjoint_of_nodup_append hc.1)
          ha (by simp only [List.mem_append, List.mem_cons]; tauto)
      have hya := lastD_ne before s a hsa haBefore
      have hg := existing_get store x (before.getLastD s) a hx hy hn hs node hNode hxa
      rw [hNextEq] at hg
      refine ⟨_, hg, ?_, ?_⟩
      · change (if some ((middle ++ a :: right).headD s) = some a then some x
          else node.prev) = some ((before ++ x :: middle).getLastD s)
        by_cases hm : middle = []
        · subst middle
          simp only [List.nil_append, List.headD_cons, ite_true, List.getLastD_concat]
        · have haMiddle : a ∉ middle := by
            intro ha
            have hnd : ((before ++ middle) ++ a :: right).Nodup := by
              simpa only [List.append_assoc] using hc.1
            exact (List.disjoint_of_nodup_append hnd)
              (List.mem_append_right before ha) List.mem_cons_self
          have hza : (middle ++ a :: right).headD s ≠ a := by
            rw [headD_append middle (a :: right) s hm]
            exact headD_ne middle s a hsa haMiddle
          simp only [Option.some.injEq, hza, ite_false, hPrev]
          rw [lastD_append before middle s hm,
            lastD_append before (x :: middle) s (List.cons_ne_nil x middle),
            List.getLastD_cons, lastD_fallback middle hm x s]
      · change (if before.getLastD s = a then some x else node.next) = some (right.headD s)
        simp only [hya, ite_false, hSucc]


/-- Insertion preserves a disjoint represented circle that excludes the inserted identity. -/
public theorem sentinelInsert_disjoint_circular {α : Type u} {n : Nat}
    (store : Vector (Option (Node α (Fin n))) n) (x y s t : Fin n)
    (ids before after other : List (Fin n))
    (hx : (store.get x).isSome) (hy : (store.get y).isSome)
    (hn : ((store.get y).get hy).next.isSome)
    (hs : ∀ z, ((store.get y).get hy).next = some z → (store.get z).isSome)
    (hc : CircularRepresents store s ids)
    (hSplit : ids = before ++ after) (hPosition : y = before.getLastD s)
    (hcOther : CircularRepresents store t other)
    (hDisjoint : List.Disjoint (s :: ids) (t :: other))
    (hFreshSentinel : x ≠ t) (hFreshData : x ∉ other) :
    CircularRepresents (sentinelInsert store x y hx hy hn hs).ret t other := by
  subst ids
  subst y
  obtain ⟨previous, hPrevious, hNext⟩ := circular_next_boundary store s before after hc
  have hPreviousGet : (store.get (before.getLastD s)).get hy = previous :=
    Option.some.inj ((Option.some_get hy).trans hPrevious)
  have hNextEq : ((store.get (before.getLastD s)).get hy).next =
      some (after.headD s) := by rw [hPreviousGet]; exact hNext
  have hyMem : before.getLastD s ∈ s :: (before ++ after) := by
    have h := @List.getLastD_mem_cons (Fin n) before s
    simp only [List.mem_cons, List.mem_append] at h ⊢
    tauto
  have hzMem : after.headD s ∈ s :: (before ++ after) := by
    cases after <;> simp
  have hxNone : x ∉ t :: other := by
    simp only [List.mem_cons, not_or]
    exact ⟨hFreshSentinel, hFreshData⟩
  have hFrame : ∀ a ∈ t :: other,
      (sentinelInsert store x (before.getLastD s) hx hy hn hs).ret.get a = store.get a := by
    intro a ha
    apply sentinelInsert_frame
    · exact fun he => hxNone (he.symm ▸ ha)
    · exact fun he => hDisjoint hyMem (he.symm ▸ ha)
    · rw [hNextEq]
      exact fun he => hDisjoint hzMem ((Option.some.inj he).symm ▸ ha)
  refine ⟨hcOther.1, hcOther.2.1, ?_, ?_⟩
  · obtain ⟨node, hNode, hNext, hPrev⟩ := hcOther.2.2.1
    exact ⟨node, (hFrame t List.mem_cons_self).trans hNode, hNext, hPrev⟩
  · intro left a right hCut
    obtain ⟨node, hNode, hPrev, hNext⟩ := hcOther.2.2.2 left a right hCut
    have ha : a ∈ t :: other := by
      simp only [hCut, List.mem_cons, List.mem_append]
      tauto
    exact ⟨node, (hFrame a ha).trans hNode, hPrev, hNext⟩


end

end Cslib.Algorithms.Lean.DoublyLinkedList
