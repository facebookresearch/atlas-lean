/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BinaryHeap
public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.WithBot
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Cslib.Algorithms.Lean.TimeM

@[expose] public section

/-!
# Indexed binary minimum queue

One canonical binary heap stores lexicographic key/identity pairs. The inverse vector
records each live identity's exact slot; swaps update only the two affected entries.
The five operations preserve the heap and inverse invariants.

The selected event tuple counts comparisons, swaps, inverse reads, inverse writes,
and entry append/pop/replacement. General indexing, allocation, copying, RAM/word/bit
and space refinements are not included. Repeated construction uses source-order INSERT.

Retained Lean is authored/repaired by Codex at Adam Kiezun's explicit selection.
-/

namespace Cslib.Algorithms.Lean.IndexedMinQueue

set_option autoImplicit false

universe u

set_option linter.dupNamespace false in
/-- A binary min-heap paired with the exact inverse location of every identity. -/
structure IndexedMinQueue (W : Type u) [LinearOrder W] (n : Nat) where
  heap : Cslib.Algorithms.Lean.MinHeap (WithTop W ×ₗ Fin n)
  position : Vector (Option (Fin n)) n
  capacity : heap.data.size ≤ n
  inverse : ∀ (v i : Fin n), position[v] = some i ↔
    ∃ hi : i.val < heap.data.size, (ofLex (heap.data[i.val]'hi)).2 = v

private def event (i : Fin 5) : Fin 5 → Nat :=
  fun j => if j = i then 1 else 0

private lemma parent_lt (i : Nat) (hi : 0 < i) : heapParent i < i := by
  unfold heapParent
  have hdiv : (i - 1) / 2 ≤ i - 1 := Nat.div_le_self _ _
  omega

private def Inverse {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n))
    (position : Vector (Option (Fin n)) n) : Prop :=
  ∀ (v i : Fin n), position[v] = some i ↔
    ∃ hi : i.val < a.size, (ofLex (a[i.val]'hi)).2 = v

private structure Tracked {W : Type u} [LinearOrder W] (n : Nat) where
  data : Array (WithTop W ×ₗ Fin n)
  position : Vector (Option (Fin n)) n
  time : Fin 5 → Nat

private def swapPosition {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n))
    (position : Vector (Option (Fin n)) n) (hcap : a.size ≤ n)
    (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    Vector (Option (Fin n)) n :=
  let vi := (ofLex (a[i]'hi)).2
  let vj := (ofLex (a[j]'hj)).2
  (position.set vi (some ⟨j, hj.trans_le hcap⟩)).set
    vj (some ⟨i, hi.trans_le hcap⟩)

private lemma inverse_indices_unique {W : Type u} [LinearOrder W] {n : Nat}
    {a : Array (WithTop W ×ₗ Fin n)}
    {position : Vector (Option (Fin n)) n} (hcap : a.size ≤ n)
    (hinv : Inverse a position) {i j : Nat} (hi : i < a.size) (hj : j < a.size)
    (hident : (ofLex (a[i]'hi)).2 = (ofLex (a[j]'hj)).2) : i = j := by
  let fi : Fin n := ⟨i, hi.trans_le hcap⟩
  let fj : Fin n := ⟨j, hj.trans_le hcap⟩
  have hpi : position[(ofLex (a[i]'hi)).2] = some fi :=
    (hinv _ fi).2 ⟨hi, rfl⟩
  have hpj : position[(ofLex (a[j]'hj)).2] = some fj :=
    (hinv _ fj).2 ⟨hj, rfl⟩
  have hposition := congrArg (fun v : Fin n => position[v]) hident
  have : fi = fj := Option.some.inj (hpi.symm.trans (hposition.trans hpj))
  exact Fin.ext_iff.mp this

private lemma absent_spare {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) (habsent : q.position[v] = none) :
    q.heap.data.size < n := by
  let f : Fin q.heap.data.size → Fin n := fun i =>
    (ofLex (q.heap.data[i.val]'i.isLt)).2
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact inverse_indices_unique q.capacity q.inverse i.isLt j.isLt hij
  have hnot : ¬ Function.Surjective f := by
    intro hsurj
    obtain ⟨i, hi⟩ := hsurj v
    let fi : Fin n := ⟨i.val, i.isLt.trans_le q.capacity⟩
    have hp : q.position[v] = some fi :=
      (q.inverse v fi).2 ⟨i.isLt, hi⟩
    rw [habsent] at hp
    contradiction
  simpa only [Fintype.card_fin] using Fintype.card_lt_of_injective_not_surjective f hinj hnot

private lemma inverse_push {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n))
    (position : Vector (Option (Fin n)) n) (hcap : a.size < n)
    (hinv : Inverse a position) (v : Fin n) (key : WithTop W)
    (habsent : position[v] = none) :
    Inverse (a.push (toLex (key, v)))
      (position.set v (some ⟨a.size, hcap⟩)) := by
  intro w i
  change (position.set v (some ⟨a.size, hcap⟩))[w.val] = some i ↔ _
  by_cases hw : w = v
  · subst w
    simp only [Vector.getElem_set]
    constructor
    · intro h
      have hi : i.val = a.size := (congrArg Fin.val (Option.some.inj h)).symm
      exact ⟨by simp [hi], by simp [Array.getElem_push, hi]⟩
    · rintro ⟨hi, hid⟩
      by_cases hilast : i.val = a.size
      · exact congrArg some (Fin.ext hilast.symm)
      · have hiold : i.val < a.size := by simp only [Array.size_push] at hi; omega
        have hp := (hinv v i).2 ⟨hiold, by simpa [Array.getElem_push_lt hiold] using hid⟩
        rw [habsent] at hp
        contradiction
  · have hwval : v.val ≠ w.val := fun h => hw (Fin.ext h.symm)
    simp only [Vector.getElem_set, ite_eq_right hwval]
    constructor
    · intro hp
      obtain ⟨hi, hid⟩ := (hinv w i).1 hp
      exact ⟨by simp only [Array.size_push]; omega,
        by simpa [Array.getElem_push_lt hi] using hid⟩
    · rintro ⟨hi, hid⟩
      have hilast : i.val ≠ a.size := by
        intro h
        exact hw (by simpa [Array.getElem_push, h] using hid.symm)
      have hiold : i.val < a.size := by simp only [Array.size_push] at hi; omega
      exact (hinv w i).2 ⟨hiold, by simpa [Array.getElem_push_lt hiold] using hid⟩

private lemma inverse_set_key {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n))
    (position : Vector (Option (Fin n)) n) (hinv : Inverse a position)
    (i : Nat) (hi : i < a.size) (v : Fin n)
    (hid : (ofLex (a[i]'hi)).2 = v) (key : WithTop W) :
    Inverse (a.set i (toLex (key, v)) hi) position := by
  intro w j
  have hidentity (hj : j.val < a.size) :
      (ofLex ((a.set i (toLex (key, v)) hi)[j.val]'(by simpa))).2 =
        (ofLex (a[j.val]'hj)).2 := by
    by_cases hji : j.val = i
    · simpa [Array.getElem_set, hji] using hid.symm
    · have hij : i ≠ j.val := fun h => hji h.symm
      simp [Array.getElem_set, hij]
  constructor
  · intro hp
    obtain ⟨hj, hentry⟩ := (hinv w j).1 hp
    exact ⟨by simpa using hj, (hidentity hj).trans hentry⟩
  · rintro ⟨hj, hentry⟩
    have hja : j.val < a.size := by simpa using hj
    exact (hinv w j).2 ⟨hja, (hidentity hja).symm.trans hentry⟩

private lemma inverse_pop_clear {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n))
    (position : Vector (Option (Fin n)) n) (hcap : a.size ≤ n)
    (hinv : Inverse a position) (hne : 0 < a.size) (v : Fin n)
    (hlast : (ofLex (a[a.size - 1]'(by omega))).2 = v) :
    Inverse a.pop (position.set v none) := by
  let last : Fin n := ⟨a.size - 1, by omega⟩
  have hlastBound : last.val < a.size := by dsimp [last]; omega
  have hplast : position[v] = some last := (hinv v last).2 ⟨hlastBound, hlast⟩
  intro w i
  change (position.set v none)[w.val] = some i ↔ _
  by_cases hw : w = v
  · subst w
    simp only [Vector.getElem_set]
    constructor
    · intro h
      contradiction
    · rintro ⟨hi, hid⟩
      have hiold : i.val < a.size := by simp only [Array.size_pop] at hi; omega
      have hp := (hinv v i).2 ⟨hiold, by simpa only [Array.getElem_pop] using hid⟩
      have hindex := congrArg Fin.val (Option.some.inj (hp.symm.trans hplast))
      simp only [Array.size_pop] at hi
      dsimp only [last] at hindex
      omega
  · have hwval : v.val ≠ w.val := fun h => hw (Fin.ext h.symm)
    simp only [Vector.getElem_set, ite_eq_right hwval]
    constructor
    · intro hp
      obtain ⟨hi, hid⟩ := (hinv w i).1 hp
      have hilast : i.val ≠ a.size - 1 := by
        intro h
        have hsame : w = v := hid.symm.trans (by simpa only [h] using hlast)
        exact hw hsame
      have hipop : i.val < a.pop.size := by simp only [Array.size_pop]; omega
      exact ⟨hipop, by simpa only [Array.getElem_pop] using hid⟩
    · rintro ⟨hi, hid⟩
      have hiold : i.val < a.size := by simp only [Array.size_pop] at hi; omega
      exact (hinv w i).2 ⟨hiold, by simpa only [Array.getElem_pop] using hid⟩

private lemma inverse_swap {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n))
    (position : Vector (Option (Fin n)) n) (hcap : a.size ≤ n)
    (hinv : Inverse a position) (i j : Nat) (hi : i < a.size) (hj : j < a.size)
    (hne : i ≠ j) :
    Inverse (a.swap i j hi hj) (swapPosition a position hcap i j hi hj) := by
  let vi := (ofLex (a[i]'hi)).2
  let vj := (ofLex (a[j]'hj)).2
  let fi : Fin n := ⟨i, hi.trans_le hcap⟩
  let fj : Fin n := ⟨j, hj.trans_le hcap⟩
  have hidne : vi ≠ vj := fun h => hne (inverse_indices_unique hcap hinv hi hj h)
  have hposition (v : Fin n) :
      (swapPosition a position hcap i j hi hj)[v] =
        if vj = v then some fi else if vi = v then some fj else position[v] := by
    change ((position.set vi.val (some fj)).set vj.val (some fi))[v.val] = _
    simp only [Vector.getElem_set, Fin.ext_iff]
    rfl
  intro v k
  rw [hposition]
  by_cases hvi : v = vi
  · subst v
    have hji : vj ≠ vi := hidne.symm
    simp only [ite_eq_right hji]
    constructor
    · intro h
      have hk : k.val = j := (congrArg Fin.val (Option.some.inj h)).symm
      refine ⟨by simp [Array.size_swap, hk, hj], ?_⟩
      simp [hk, vi]
    · rintro ⟨hk, hid⟩
      have hka : k.val < a.size := by simpa only [Array.size_swap] using hk
      by_cases hki : k.val = i
      · have hbad : vj = vi := by simpa [Array.getElem_swap, hki, vj] using hid
        exact (hji hbad).elim
      · by_cases hkj : k.val = j
        · exact congrArg some (Fin.ext hkj.symm)
        · have hold : (ofLex (a[k.val]'hka)).2 = vi := by
            simpa [Array.getElem_swap, hki, hkj] using hid
          have heq := inverse_indices_unique hcap hinv hka hi hold
          exact (hki heq).elim
  · by_cases hvj : v = vj
    · subst v
      rw [ite_eq_left rfl]
      constructor
      · intro h
        have hk : k.val = i := (congrArg Fin.val (Option.some.inj h)).symm
        refine ⟨by simp [Array.size_swap, hk, hi], ?_⟩
        simp [hk, vj]
      · rintro ⟨hk, hid⟩
        have hka : k.val < a.size := by simpa only [Array.size_swap] using hk
        by_cases hki : k.val = i
        · exact congrArg some (Fin.ext hki.symm)
        · by_cases hkj : k.val = j
          · have hbad : vi = vj := by simpa [Array.getElem_swap, hki, hkj, vi] using hid
            exact (hidne hbad).elim
          · have hold : (ofLex (a[k.val]'hka)).2 = vj := by
              simpa [Array.getElem_swap, hki, hkj] using hid
            have heq := inverse_indices_unique hcap hinv hka hj hold
            exact (hkj heq).elim
    · have hvjne : vj ≠ v := fun h => hvj h.symm
      have hvine : vi ≠ v := fun h => hvi h.symm
      simp only [ite_eq_right hvjne, ite_eq_right hvine]
      constructor
      · intro hp
        obtain ⟨hk, hid⟩ := (hinv v k).1 hp
        have hki : k.val ≠ i := by
          intro h
          exact hvi (by simpa [h, vi] using hid.symm)
        have hkj : k.val ≠ j := by
          intro h
          exact hvj (by simpa [h, vj] using hid.symm)
        exact ⟨by simpa only [Array.size_swap] using hk,
          by simpa [Array.getElem_swap, hki, hkj] using hid⟩
      · rintro ⟨hk, hid⟩
        have hka : k.val < a.size := by simpa only [Array.size_swap] using hk
        have hki : k.val ≠ i := by
          intro h
          exact hvj (by simpa [Array.getElem_swap, h, vj] using hid.symm)
        have hkj : k.val ≠ j := by
          intro h
          exact hvi (by simpa [Array.getElem_swap, h, hne.symm, vi] using hid.symm)
        exact (hinv v k).2 ⟨hka, by simpa [Array.getElem_swap, hki, hkj] using hid⟩

private def siftUpTracked {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n))
    (position : Vector (Option (Fin n)) n) (hcap : a.size ≤ n)
    (i : Nat) : Tracked (W := W) n :=
  if hi : i < a.size then
    if hpos : 0 < i then
      let p := heapParent i
      let hp := heapParent_lt_size a i hi hpos
      if a[i] < a[p] then
        let a' := a.swap i p hi hp
        let position' := swapPosition a position hcap i p hi hp
        let r := siftUpTracked a' position' (by simpa [a'] using hcap) p
        ⟨r.data, r.position,
          event 0 + event 1 + event 3 + event 3 + r.time⟩
      else
        ⟨a, position, event 0⟩
    else
      ⟨a, position, 0⟩
  else
    ⟨a, position, 0⟩
termination_by i
decreasing_by
  exact parent_lt i hpos

private def childSelectionTime {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n)) (i : Nat) : Fin 5 → Nat :=
  if heapRight i < a.size then event 0 else 0

private def siftDownTracked {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n))
    (position : Vector (Option (Fin n)) n) (hcap : a.size ≤ n)
    (i : Nat) : Tracked (W := W) n :=
  match hchild : smallerChild a i with
  | none => ⟨a, position, 0⟩
  | some c =>
    have hc : c < a.size := smallerChild_valid a i c hchild
    have hi : i < a.size := (smallerChild_gt a i c hchild).trans hc
    let chooseTime := childSelectionTime a i
    if a[c] < a[i] then
      let a' := a.swap i c hi hc
      let position' := swapPosition a position hcap i c hi hc
      let r := siftDownTracked a' position' (by simpa [a'] using hcap) c
      ⟨r.data, r.position,
        chooseTime + event 0 + event 1 + event 3 + event 3 + r.time⟩
    else
      ⟨a, position, chooseTime + event 0⟩
termination_by a.size - i
decreasing_by
  simp only [Array.size_swap]
  have := smallerChild_gt a i c hchild
  omega

private lemma siftUpTracked_data {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n))
    (position : Vector (Option (Fin n)) n) (hcap : a.size ≤ n) (i : Nat) :
    (siftUpTracked a position hcap i).data = siftUp a i := by
  induction i using Nat.strong_induction_on generalizing a position with
  | h i ih =>
    rw [siftUpTracked, siftUp]
    by_cases hi : i < a.size
    · simp only [dite_eq_left hi]
      by_cases hpos : 0 < i
      · simp only [dite_eq_left hpos]
        split
        · exact ih (heapParent i) (parent_lt i hpos) _ _ _
        · rfl
      · simp only [dite_eq_right hpos]
    · simp only [dite_eq_right hi]

private lemma siftDownTracked_data {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n))
    (position : Vector (Option (Fin n)) n) (hcap : a.size ≤ n) (i : Nat) :
    (siftDownTracked a position hcap i).data = siftDown a i := by
  induction hm : a.size - i using Nat.strong_induction_on generalizing a position i with
  | h m ih =>
    rw [siftDownTracked]
    split
    · rename_i hnone
      rw [siftDown]
      split
      · rfl
      · rename_i c hsome
        simp_all
    · rename_i c hchild
      rw [siftDown]
      split
      · simp_all
      · rename_i c' hchild'
        have heq : c = c' := Option.some.inj (hchild.symm.trans hchild')
        subst c'
        dsimp only
        have hc := smallerChild_valid a i c hchild
        have hi := (smallerChild_gt a i c hchild).trans hc
        by_cases hlt : a[c] < a[i]
        · simp only [ite_eq_left hlt, dite_eq_left hlt]
          refine ih (a.size - c) ?_ _ _ _ c ?_
          · have := smallerChild_gt a i c hchild
            omega
          · simp only [Array.size_swap]
        · simp only [ite_eq_right hlt, dite_eq_right hlt]

private lemma siftUpTracked_inverse {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n))
    (position : Vector (Option (Fin n)) n) (hcap : a.size ≤ n)
    (hinv : Inverse a position) (i : Nat) :
    Inverse (siftUpTracked a position hcap i).data
      (siftUpTracked a position hcap i).position := by
  induction i using Nat.strong_induction_on generalizing a position with
  | h i ih =>
    rw [siftUpTracked]
    split
    · rename_i hi
      split
      · rename_i hpos
        dsimp only
        by_cases hlt : a[i] < a[heapParent i]'(heapParent_lt_size a i hi hpos)
        · simp only [ite_eq_left hlt]
          apply ih (heapParent i) (parent_lt i hpos)
          exact inverse_swap a position hcap hinv i (heapParent i) hi
            (heapParent_lt_size a i hi hpos) (Nat.ne_of_gt (parent_lt i hpos))
        · simpa only [ite_eq_right hlt] using hinv
      · exact hinv
    · exact hinv

private lemma siftDownTracked_inverse {W : Type u} [LinearOrder W] {n : Nat}
    (a : Array (WithTop W ×ₗ Fin n))
    (position : Vector (Option (Fin n)) n) (hcap : a.size ≤ n)
    (hinv : Inverse a position) (i : Nat) :
    Inverse (siftDownTracked a position hcap i).data
      (siftDownTracked a position hcap i).position := by
  induction hm : a.size - i using Nat.strong_induction_on generalizing a position i with
  | h m ih =>
    rw [siftDownTracked]
    split
    · exact hinv
    · rename_i c hchild
      dsimp only
      split
      · refine ih (a.size - c) ?_ _ _ _ ?_ c ?_
        · have := smallerChild_gt a i c hchild
          have := smallerChild_valid a i c hchild
          omega
        · exact inverse_swap a position hcap hinv i c
            ((smallerChild_gt a i c hchild).trans (smallerChild_valid a i c hchild))
            (smallerChild_valid a i c hchild) (Nat.ne_of_lt (smallerChild_gt a i c hchild))
        · simp only [Array.size_swap]
      · exact hinv

/-- The empty indexed queue has the canonical empty heap and no present identity. -/
def empty {W : Type u} [LinearOrder W] (n : Nat) : IndexedMinQueue W n where
  heap := MinHeap.empty
  position := Vector.replicate n none
  capacity := by simp [MinHeap.empty]
  inverse := by simp [MinHeap.empty]

/-- Test membership by one inverse-vector read. -/
@[no_expose] def member {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) : TimeM (Fin 5 → Nat) Bool :=
  ⟨q.position[v].isSome, event 2⟩

/-- Insert one absent identity, rejecting an identity already in the queue. -/
@[no_expose] def insert {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) (key : WithTop W) :
    TimeM (Fin 5 → Nat) (Option (IndexedMinQueue W n)) :=
  if hpresent : q.position[v].isSome = true then
    ⟨none, event 2⟩
  else
    have habsent : q.position[v] = none := by
      simpa [Option.isSome_iff_ne_none] using hpresent
    have hspare : q.heap.data.size < n := absent_spare q v habsent
    let entry := toLex (key, v)
    let a := q.heap.data.push entry
    let position := q.position.set v (some ⟨q.heap.data.size, hspare⟩)
    let hcap : a.size ≤ n := by simp [a]; omega
    let r := siftUpTracked a position hcap q.heap.data.size
    have hrdata : r.data = (q.heap.push entry).data := by
      exact siftUpTracked_data a position hcap q.heap.data.size
    have hrinv : Inverse r.data r.position := by
      apply siftUpTracked_inverse a position hcap
      exact inverse_push q.heap.data q.position hspare q.inverse v key habsent
    let heap' : MinHeap (WithTop W ×ₗ Fin n) :=
      ⟨r.data, by rw [hrdata]; exact (q.heap.push entry).ordered⟩
    have hcap' : heap'.data.size ≤ n := by
      rw [show heap'.data = r.data from rfl, hrdata]
      change (siftUp a q.heap.data.size).size ≤ n
      rw [(siftUp_perm a q.heap.data.size).size_eq]
      exact hcap
    ⟨some ⟨heap', r.position, hcap', hrinv⟩,
      event 2 + event 3 + event 4 + r.time⟩

private lemma set_decrease_ready {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) (key : W) (i : Fin n)
    (hi : i.val < q.heap.data.size) (_hid : (ofLex (q.heap.data[i.val]'hi)).2 = v)
    (hlt : (↑key : WithTop W) < (ofLex (q.heap.data[i.val]'hi)).1) :
    SiftUpReady
      (q.heap.data.set i.val (toLex ((↑key : WithTop W), v)) hi) i.val := by
  refine {
    index_valid := by simpa using hi
    ordered_except := ?_
    parent_below_children := ?_
  }
  · intro j hj hjpos hji
    have hjold : j < q.heap.data.size := by simpa using hj
    have hpold : heapParent j < q.heap.data.size := heapParent_lt_size _ _ hjold hjpos
    have hold := q.heap.ordered j hjold hjpos
    simp only [Array.getElem_set]
    rw [ite_eq_right hji.symm]
    by_cases hp : heapParent j = i.val
    · rw [ite_eq_left hp.symm]
      have hlex : toLex ((↑key : WithTop W), v) ≤ q.heap.data[i.val]'hi := by
          rw [Prod.Lex.le_iff]
          exact Or.inl hlt
      exact hlex.trans (by simpa only [hp] using hold)
    · simpa [Ne.symm hp] using hold
  · intro j hj hjpos hp hipos
    have hjold : j < q.heap.data.size := by simpa using hj
    have hparentold : heapParent i.val < q.heap.data.size :=
      heapParent_lt_size _ _ hi hipos
    have hold := q.heap.ordered j hjold hjpos
    have hparent_ne : heapParent i.val ≠ i.val := (parent_lt i.val hipos).ne
    have hji : j ≠ i.val := by
      intro h
      subst h
      exact (parent_lt i.val hipos).ne hp
    have hparent := q.heap.ordered i.val hi hipos
    have hchild : q.heap.data[i.val]'hi ≤ q.heap.data[j]'hjold := by
      simpa only [hp] using hold
    simpa only [Array.getElem_set, ite_eq_right hparent_ne.symm,
      ite_eq_right hji.symm] using hparent.trans hchild

/-- Strictly lower the finite key of one present identity and sift it upward. -/
@[no_expose] def decreaseKey {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) (key : W) :
    TimeM (Fin 5 → Nat) (Option (IndexedMinQueue W n)) :=
  match hp : q.position[v] with
  | none => ⟨none, event 2⟩
  | some i =>
    have hi : i.val < q.heap.data.size := (q.inverse v i).1 hp |>.choose
    let old := q.heap.data[i.val]'hi
    if hlt : (↑key : WithTop W) < (ofLex old).1 then
      have hid : (ofLex old).2 = v := (q.inverse v i).1 hp |>.choose_spec
      let a := q.heap.data.set i.val (toLex ((↑key : WithTop W), v)) hi
      have hinv : Inverse a q.position :=
        inverse_set_key q.heap.data q.position q.inverse i.val hi v hid key
      let r := siftUpTracked a q.position (by simpa [a] using q.capacity) i.val
      have hrinv := siftUpTracked_inverse a q.position (by simpa [a] using q.capacity) hinv i.val
      let heap' : MinHeap (WithTop W ×ₗ Fin n) :=
        ⟨r.data, by
          rw [siftUpTracked_data]
          exact siftUp_ordered a i.val (set_decrease_ready q v key i hi hid hlt)⟩
      let q' : IndexedMinQueue W n :=
        ⟨heap', r.position, by
          rw [show heap'.data = r.data from rfl, siftUpTracked_data]
          rw [(siftUp_perm a i.val).size_eq]
          simpa [a] using q.capacity, hrinv⟩
      ⟨some q', event 2 + event 0 + event 4 + r.time⟩
    else
      ⟨none, event 2 + event 0⟩

/-- Remove and return the canonical minimum, rejecting only the empty queue. -/
@[no_expose] def extractMin {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) :
    TimeM (Fin 5 → Nat)
      (Option ((WithTop W ×ₗ Fin n) × IndexedMinQueue W n)) :=
  if hempty : q.heap.data.size = 0 then
    ⟨none, 0⟩
  else
    have hne : 0 < q.heap.data.size := Nat.pos_of_ne_zero hempty
    let entry := q.heap.data[0]'hne
    let v := (ofLex entry).2
    if hone : q.heap.data.size = 1 then
      let position := q.position.set v none
      have hinv : Inverse (#[] : Array (WithTop W ×ₗ Fin n)) position := by
        have hlast : (ofLex (q.heap.data[q.heap.data.size - 1]'(by omega))).2 = v := by
          simp [v, entry, hone]
        have hpop : q.heap.data.pop = #[] :=
          Array.eq_empty_of_size_eq_zero (by simp [hone])
        simpa only [hpop] using
          inverse_pop_clear q.heap.data q.position q.capacity q.inverse hne v hlast
      let q' : IndexedMinQueue W n :=
        ⟨MinHeap.empty, position, by simp [MinHeap.empty], hinv⟩
      ⟨some (entry, q'), event 3 + event 4⟩
    else
      have htwo : 1 < q.heap.data.size := by omega
      let last := q.heap.data.size - 1
      let aSwap := q.heap.data.swap 0 last hne (by dsimp [last]; omega)
      let positionSwap := swapPosition q.heap.data q.position q.capacity 0 last hne
        (by dsimp [last]; omega)
      have hinvSwap : Inverse aSwap positionSwap := by
        apply inverse_swap q.heap.data q.position q.capacity q.inverse 0 last hne
          (by dsimp [last]; omega)
        omega
      let a := aSwap.pop
      let position := positionSwap.set v none
      have hlast : (ofLex (aSwap[aSwap.size - 1]'(by
          dsimp only [aSwap]
          rw [Array.size_swap]
          omega))).2 = v := by
        simp [aSwap, last, v, entry]
      have hinv : Inverse a position := by
        exact inverse_pop_clear aSwap positionSwap (by simpa [aSwap] using q.capacity)
          hinvSwap (by simp [aSwap]; omega) v hlast
      have hcap : a.size ≤ n := by
        have hc := q.capacity
        simp only [a, aSwap, Array.size_pop, Array.size_swap]
        omega
      let r := siftDownTracked a position hcap 0
      have hrdata : r.data = (q.heap.extractTail hne).data := by
        rw [MinHeap.extractTail, dite_eq_right hone]
        exact siftDownTracked_data a position hcap 0
      have hrinv := siftDownTracked_inverse a position hcap hinv 0
      let heap' : MinHeap (WithTop W ×ₗ Fin n) :=
        ⟨r.data, by rw [hrdata]; exact (q.heap.extractTail hne).ordered⟩
      let q' : IndexedMinQueue W n :=
        ⟨heap', r.position, by
          change r.data.size ≤ n
          rw [siftDownTracked_data, (siftDown_perm a 0).size_eq]
          exact hcap, hrinv⟩
      ⟨some (entry, q'),
        event 1 + event 3 + event 3 + event 3 + event 4 + r.time⟩

end Cslib.Algorithms.Lean.IndexedMinQueue
