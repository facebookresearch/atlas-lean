/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.IndexedMinQueue.Basic
import all CSLibExt.Algorithms.Lean.DataStructures.IndexedMinQueue.Basic

@[expose] public section

/-!
# Indexed minimum queue return specifications

The public laws refine the executed operations to the existing canonical binary heap
and preserve identity membership. All inverse/array proof support remains private.

Retained Lean is authored/repaired by Codex at Adam Kiezun's explicit selection.
-/

namespace Cslib.Algorithms.Lean.IndexedMinQueue

set_option autoImplicit false

universe u

/-- Every stored inverse slot lies within the current heap. -/
theorem position_valid {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v i : Fin n)
    (h : q.position[v] = some i) : i.val < q.heap.data.size := by
  exact (q.inverse v i).1 h |>.choose

/-- An identity is absent exactly when no heap entry carries it. -/
theorem position_eq_none_iff {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) :
    q.position[v] = none ↔
      ¬ ∃ entry ∈ q.heap.data.toList, (ofLex entry).2 = v := by
  constructor
  · intro hp ⟨entry, hmem, hid⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
    let fi : Fin n := ⟨i, by simpa using hi.trans_le q.capacity⟩
    have := (q.inverse v fi).2 ⟨by simpa using hi, hid⟩
    simp [hp] at this
  · intro hnot
    cases hp : q.position[v] with
    | none => rfl
    | some i =>
      exfalso
      obtain ⟨hi, hid⟩ := (q.inverse v i).1 hp
      apply hnot
      exact ⟨q.heap.data[i.val]'hi, by simp [Array.mem_toList_iff], hid⟩

/-- The empty queue marks every identity absent. -/
theorem empty_position {W : Type u} [LinearOrder W] {n : Nat}
    (v : Fin n) : (empty (W := W) n).position[v] = none := by
  simp [empty]

/-- INSERT rejects exactly the identities already present. -/
theorem insert_eq_none_iff {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) (key : WithTop W) :
    (insert q v key).ret = none ↔ q.position[v].isSome = true := by
  unfold insert
  split
  · rename_i hp
    dsimp only
    simp only [hp, iff_self]
  · rename_i hp
    dsimp only
    simp only [Option.some_ne_none, false_iff]
    exact hp

/-- EXTRACT-MIN rejects exactly an empty heap. -/
theorem extractMin_eq_none_iff {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) :
    (extractMin q).ret = none ↔ q.heap.data.size = 0 := by
  unfold extractMin
  split
  · simp_all
  · dsimp only
    split <;> dsimp only <;> simp_all

/-- Membership returns the actual inverse-vector presence flag. -/
theorem member_ret {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) :
    (member q v).ret = q.position[v].isSome := by
  unfold member
  rfl

/-- Membership performs exactly one selected inverse read. -/
theorem member_time {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) :
    (member q v).time = fun c : Fin 5 => if c = 2 then 1 else 0 := by
  unfold member event
  rfl

private lemma heap_eq_of_data_eq {α : Type u} [LinearOrder α]
    (h h' : MinHeap α) (heq : h.data = h'.data) : h = h' := by
  cases h
  cases h'
  cases heq
  rfl

private lemma position_isSome_iff {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) :
    q.position[v].isSome = true ↔
      ∃ entry ∈ q.heap.data.toList, (ofLex entry).2 = v := by
  rw [Option.isSome_iff_ne_none, ne_eq, position_eq_none_iff]
  exact not_not

private lemma position_isSome_eq_of_mem_iff {W : Type u} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (v : Fin n)
    (h : (∃ entry ∈ q'.heap.data.toList, (ofLex entry).2 = v) ↔
      ∃ entry ∈ q.heap.data.toList, (ofLex entry).2 = v) :
    q'.position[v].isSome = q.position[v].isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [position_isSome_iff, position_isSome_iff]
  exact h

private lemma insert_heap_eq {W : Type u} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (v : Fin n) (key : WithTop W)
    (h : (insert q v key).ret = some q') :
    q'.heap = q.heap.push (toLex (key, v)) := by
  unfold insert at h
  split at h
  · contradiction
  · dsimp only at h
    simp only [Option.some.injEq] at h
    subst q'
    apply heap_eq_of_data_eq
    exact siftUpTracked_data _ _ _ _

/-- Successful INSERT refines canonical push and preserves all other identities. -/
theorem insert_ret {W : Type u} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (v : Fin n) (key : WithTop W)
    (h : (insert q v key).ret = some q') :
    q'.heap = q.heap.push (toLex (key, v)) ∧
      (∃ (i : Fin n) (hi : i.val < q'.heap.data.size),
        q'.position[v] = some i ∧ q'.heap.data[i.val]'hi = toLex (key, v)) ∧
      ∀ w : Fin n, w ≠ v → q'.position[w].isSome = q.position[w].isSome := by
  have hh := insert_heap_eq q q' v key h
  refine ⟨hh, ?_, ?_⟩
  · have hmem : toLex (key, v) ∈ q'.heap.data.toList := by
      change toLex (key, v) ∈ q'.heap.elements
      rw [hh, MinHeap.elements_push]
      simp
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hmem
    have his : i < q'.heap.data.size := by simpa using hi
    let fi : Fin n := ⟨i, his.trans_le q'.capacity⟩
    refine ⟨fi, his, ?_, ?_⟩
    · apply (q'.inverse v fi).2
      refine ⟨his, ?_⟩
      simpa using congrArg (fun e => (ofLex e).2) he
    · simpa using he
  · intro w hw
    apply position_isSome_eq_of_mem_iff q q' w
    constructor
    · rintro ⟨entry, he, hid⟩
      change entry ∈ q'.heap.elements at he
      rw [hh, MinHeap.elements_push] at he
      simp only [Multiset.mem_cons] at he
      rcases he with he | he
      · subst entry
        exact False.elim (hw (by simpa using hid.symm))
      · exact ⟨entry, he, hid⟩
    · rintro ⟨entry, he, hid⟩
      refine ⟨entry, ?_, hid⟩
      change entry ∈ q'.heap.elements
      rw [hh, MinHeap.elements_push]
      simp only [Multiset.mem_cons]
      exact Or.inr he

private lemma inverse_none_iff {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n)) (position : Vector (Option (Fin n)) n)
    (hcap : a.size ≤ n) (hinv : Inverse a position) (v : Fin n) :
    position[v] = none ↔ ¬ ∃ entry ∈ a.toList, (ofLex entry).2 = v := by
  constructor
  · intro hp ⟨entry, hmem, hid⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
    have his : i < a.size := by simpa using hi
    let fi : Fin n := ⟨i, his.trans_le hcap⟩
    have he := (hinv v fi).2 ⟨his, hid⟩
    simp [hp] at he
  · intro hnot
    cases hp : position[v] with
    | none => rfl
    | some i =>
      exfalso
      obtain ⟨hi, hid⟩ := (hinv v i).1 hp
      apply hnot
      exact ⟨a[i.val]'hi, by simp [Array.mem_toList_iff], hid⟩

private lemma inverse_isSome_eq_of_perm {W : Type u} [LinearOrder W] {n : Nat}
    (a b : Array (WithTop W ×ₗ Fin n))
    (p p' : Vector (Option (Fin n)) n) (ha : a.size ≤ n) (hb : b.size ≤ n)
    (hia : Inverse a p) (hib : Inverse b p') (hperm : b.Perm a) (v : Fin n) :
    p'[v].isSome = p[v].isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [Option.isSome_iff_ne_none, Option.isSome_iff_ne_none]
  simp only [ne_eq, inverse_none_iff a p ha hia,
    inverse_none_iff b p' hb hib, not_not]
  constructor
  · rintro ⟨entry, he, hid⟩
    refine ⟨entry, ?_, hid⟩
    rw [Array.mem_toList_iff] at he ⊢
    exact hperm.mem_iff.mp he
  · rintro ⟨entry, he, hid⟩
    refine ⟨entry, ?_, hid⟩
    rw [Array.mem_toList_iff] at he ⊢
    exact hperm.mem_iff.mpr he

/-- DECREASE-KEY rejects absent identities and non-strict decreases. -/
theorem decreaseKey_eq_none_iff {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) (key : W) :
    (decreaseKey q v key).ret = none ↔
      q.position[v] = none ∨
        ∃ (i : Fin n) (hi : i.val < q.heap.data.size),
          q.position[v] = some i ∧
            ¬ (↑key : WithTop W) < (ofLex (q.heap.data[i.val]'hi)).1 := by
  unfold decreaseKey
  split
  · rename_i hp
    dsimp only
    simp only [true_iff]
    exact Or.inl hp
  · rename_i i hp
    dsimp only
    split
    · rename_i hlt
      dsimp only
      simp only [Option.some_ne_none, false_iff]
      rintro (hnone | ⟨j, hj, hpj, hnlt⟩)
      · rw [hp] at hnone
        contradiction
      · have hij : i = j := Option.some.inj (hp.symm.trans hpj)
        subst j
        exact hnlt hlt
    · rename_i hnlt
      dsimp only
      simp only [true_iff]
      exact Or.inr ⟨i, position_valid q v i hp, hp, hnlt⟩

/-- A successful decrease replaces its key and preserves every identity. -/
theorem decreaseKey_ret {W : Type u} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (v : Fin n) (key : W)
    (h : (decreaseKey q v key).ret = some q') :
    (∃ (i : Fin n) (hi : i.val < q.heap.data.size),
      q.position[v] = some i ∧
        (↑key : WithTop W) < (ofLex (q.heap.data[i.val]'hi)).1 ∧
        q'.heap.data = siftUp
          (q.heap.data.set i.val (toLex ((↑key : WithTop W), v)) hi) i.val) ∧
      ∀ w : Fin n, q'.position[w].isSome = q.position[w].isSome := by
  unfold decreaseKey at h
  split at h
  · contradiction
  · rename_i i hp
    dsimp only at h
    split at h
    · rename_i hlt
      dsimp only at h
      simp only [Option.some.injEq] at h
      subst q'
      have hi := position_valid q v i hp
      refine ⟨⟨i, hi, hp, hlt, ?_⟩, ?_⟩
      · exact siftUpTracked_data _ _ _ _
      · intro w
        let a := q.heap.data.set i.val (toLex ((↑key : WithTop W), v)) hi
        have hc : a.size ≤ n := by simpa only [a, Array.size_set] using q.capacity
        have hid : (ofLex (q.heap.data[i.val]'hi)).2 = v :=
          (q.inverse v i).1 hp |>.choose_spec
        have hia : Inverse a q.position :=
          inverse_set_key q.heap.data q.position q.inverse i.val hi v hid key
        have hib := siftUpTracked_inverse a q.position hc hia i.val
        have hcb : (siftUpTracked a q.position hc i.val).data.size ≤ n := by
          rw [siftUpTracked_data, (siftUp_perm a i.val).size_eq]
          exact hc
        exact inverse_isSome_eq_of_perm a (siftUpTracked a q.position hc i.val).data
          q.position (siftUpTracked a q.position hc i.val).position hc hcb hia hib
          (by rw [siftUpTracked_data]; exact siftUp_perm a i.val) w
    · contradiction

private lemma extract_heap_eq {W : Type u} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (h : (extractMin q).ret = some (entry, q')) :
    q.heap.extractMin = some (entry, q'.heap) := by
  unfold extractMin at h
  split at h
  · contradiction
  · rename_i hempty
    dsimp only at h
    split at h
    · rename_i hone
      dsimp only at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      unfold MinHeap.extractMin
      rw [dite_eq_left (show 0 < q.heap.data.size by omega)]
      simp only [MinHeap.extractTail, dite_eq_left hone]
    · rename_i hone
      dsimp only at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      unfold MinHeap.extractMin
      rw [dite_eq_left (show 0 < q.heap.data.size by omega)]
      congr 1
      congr 1
      apply heap_eq_of_data_eq
      simp only [MinHeap.extractTail, dite_eq_right hone]
      exact (siftDownTracked_data _ _ _ _).symm

private lemma siftDownTracked_none {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n)) (p : Vector (Option (Fin n)) n)
    (hcap : a.size ≤ n) (hinv : Inverse a p) (v : Fin n)
    (hp : p[v] = none) (i : Nat) :
    (siftDownTracked a p hcap i).position[v] = none := by
  have hib := siftDownTracked_inverse a p hcap hinv i
  have hcb : (siftDownTracked a p hcap i).data.size ≤ n := by
    rw [siftDownTracked_data, (siftDown_perm a i).size_eq]
    exact hcap
  have he := inverse_isSome_eq_of_perm a (siftDownTracked a p hcap i).data
    p (siftDownTracked a p hcap i).position hcap hcb hinv hib
    (by rw [siftDownTracked_data]; exact siftDown_perm a i) v
  cases hr : (siftDownTracked a p hcap i).position[v] with
  | none => rfl
  | some j => simp [hr, hp] at he

private lemma extract_position_none {W : Type u} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (h : (extractMin q).ret = some (entry, q')) :
    q'.position[(ofLex entry).2] = none := by
  unfold extractMin at h
  split at h
  · contradiction
  · rename_i hempty
    dsimp only at h
    split at h
    · dsimp only at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp
    · dsimp only at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have hne : 0 < q.heap.data.size := by omega
      have hj : q.heap.data.size - 1 < q.heap.data.size := by omega
      let aSwap := q.heap.data.swap 0 (q.heap.data.size - 1) hne hj
      let pSwap := swapPosition q.heap.data q.position q.capacity 0
        (q.heap.data.size - 1) hne hj
      let v := (ofLex (q.heap.data[0]'hne)).2
      have hc : aSwap.size ≤ n := by simpa only [aSwap, Array.size_swap] using q.capacity
      have his : Inverse aSwap pSwap :=
        inverse_swap q.heap.data q.position q.capacity q.inverse 0
          (q.heap.data.size - 1) hne hj (by omega)
      have hpos : 0 < aSwap.size := by simpa only [aSwap, Array.size_swap] using hne
      have hlast : (ofLex (aSwap[aSwap.size - 1]'(by omega))).2 = v := by
        simp [aSwap, v]
      have hip : Inverse aSwap.pop (pSwap.set v none) :=
        inverse_pop_clear aSwap pSwap hc his hpos v hlast
      have hcp : aSwap.pop.size ≤ n := by
        simp only [Array.size_pop]
        omega
      exact siftDownTracked_none aSwap.pop (pSwap.set v none) hcp hip v
        (by simp) 0

/-- Successful extraction refines canonical extraction and removes only its identity. -/
theorem extractMin_ret {W : Type u} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (h : (extractMin q).ret = some (entry, q')) :
    q.heap.extractMin = some (entry, q'.heap) ∧
      q'.position[(ofLex entry).2] = none ∧
      ∀ w : Fin n, w ≠ (ofLex entry).2 →
        q'.position[w].isSome = q.position[w].isSome := by
  have hh := extract_heap_eq q q' entry h
  refine ⟨hh, extract_position_none q q' entry h, ?_⟩
  intro w hw
  apply position_isSome_eq_of_mem_iff q q' w
  constructor
  · rintro ⟨e, he, hid⟩
    have hne : e ≠ entry := by
      intro heq
      subst e
      exact hw hid.symm
    exact ⟨e, (MinHeap.extractMin_mem_of_ne_iff hh hne).mp he, hid⟩
  · rintro ⟨e, he, hid⟩
    have hne : e ≠ entry := by
      intro heq
      subst e
      exact hw hid.symm
    exact ⟨e, (MinHeap.extractMin_mem_of_ne_iff hh hne).mpr he, hid⟩

end Cslib.Algorithms.Lean.IndexedMinQueue
