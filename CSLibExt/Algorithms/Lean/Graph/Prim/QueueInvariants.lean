/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.Prim.Basic
import CSLibExt.Algorithms.Lean.DataStructures.IndexedMinQueue
import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency
import Cslib.Algorithms.Lean.TimeM
import Mathlib.Data.Sym.Sym2

/-!
# Prim queue and extraction invariants

Adapted from CLRS, fourth edition, section 21.2, Prim's algorithm.
Proofs and executable code authored with Codex under Adam Kiezun's authorization.
-/

open Cslib.Algorithms.Lean

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe u

private lemma queueKey_some {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v i : Fin n) (hp : q.position[v] = some i) :
    queueKey q v = (ofLex (q.heap.data[i.val]'(position_valid q v i hp))).1 := by
  unfold queueKey
  split
  · rename_i hn
    cases hp.symm.trans hn
  · rename_i j hj
    have hij : i = j := Option.some.inj (hp.symm.trans hj)
    subst j
    rfl

private lemma insert_succeeds {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) (key : WithTop W)
    (hp : q.position[v] = none) : ∃ q', (insert q v key).ret = some q' := by
  cases h : (insert q v key).ret with
  | none =>
    have impossible := (insert_eq_none_iff q v key).mp h
    simp [hp] at impossible
  | some q' => exact ⟨q', rfl⟩

private lemma decrease_succeeds {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) (key : W)
    (hlive : (Cslib.Algorithms.Lean.IndexedMinQueue.member q v).ret = true)
    (hlt : (key : WithTop W) < queueKey q v) :
    ∃ q', (decreaseKey q v key).ret = some q' := by
  have hpresent : q.position[v].isSome = true := by
    simpa only [member_ret] using hlive
  cases hp : q.position[v] with
  | none => simp [hp] at hpresent
  | some i =>
    have hi := position_valid q v i hp
    rw [queueKey_some q v i hp] at hlt
    cases hd : (decreaseKey q v key).ret with
    | some q' => exact ⟨q', rfl⟩
    | none =>
      rcases (decreaseKey_eq_none_iff q v key).mp hd with hn | ⟨j, hj, hpj, hnot⟩
      · cases hp.symm.trans hn
      · have hij : i = j := Option.some.inj (hp.symm.trans hpj)
        subst j
        exact (hnot hlt).elim

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe u

private lemma initQueue_presence {W : Type u} [LinearOrder W] [Zero W] {n : Nat}
    (root : Fin n) (vs : List (Fin n)) (q : IndexedMinQueue W n)
    (hn : vs.Nodup) (ha : ∀ v ∈ vs, q.position[v] = none) :
    ∀ w : Fin n, (initQueue root vs q).ret.position[w].isSome =
      if w ∈ vs then true else q.position[w].isSome := by
  induction vs generalizing q with
  | nil => simp [initQueue]
  | cons v vs ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
    have hv := ha v (by simp)
    obtain ⟨q', hins⟩ := insert_succeeds q v
      (if v = root then (0 : W) else ⊤) hv
    have hspec := insert_ret q q' v (if v = root then (0 : W) else ⊤) hins
    have hpv : q'.position[v].isSome = true := by
      obtain ⟨i, hi, hp, he⟩ := hspec.2.1
      simp [hp]
    have habsent : ∀ w ∈ vs, q'.position[w] = none := by
      intro w hw
      have hwv : w ≠ v := by
        intro h
        subst w
        exact hnot hw
      have hflag := hspec.2.2 w hwv
      have hp := ha w (List.mem_cons_of_mem v hw)
      rw [hp] at hflag
      cases hp' : q'.position[w] with
      | none => rfl
      | some i => simp [hp'] at hflag
    have hrun : (initQueue root (v :: vs) q).ret = (initQueue root vs q').ret := by
      simp only [initQueue, TimeM.ret_bind, liftHeap, hins]
    intro w
    rw [hrun, ih q' htail habsent w]
    by_cases hw : w = v
    · subst w
      rw [ite_eq_right hnot, ite_eq_left (by simp)]
      exact hpv
    · rw [hspec.2.2 w hw]
      simp [List.mem_cons, hw]

private lemma initQueue_full {W : Type u} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (root v : Fin n) :
    (initQueue (W := W) root graph.vertices (empty n)).ret.position[v].isSome = true := by
  rw [initQueue_presence root graph.vertices (empty n) graph.vertices_nodup
    (fun w _ => empty_position w) v]
  simp [graph.vertices_complete v]

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uprd1

private lemma insert_size {W : Type uprd1} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (v : Fin n) (key : WithTop W)
    (h : (insert q v key).ret = some q') :
    q'.heap.data.size = q.heap.data.size + 1 := by
  have hc := congrArg Multiset.card (MinHeap.elements_push q.heap (toLex (key, v)))
  rw [← (insert_ret q q' v key h).1] at hc
  simpa [MinHeap.elements] using hc

private lemma decrease_size {W : Type uprd1} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (v : Fin n) (key : W)
    (h : (decreaseKey q v key).ret = some q') :
    q'.heap.data.size = q.heap.data.size := by
  obtain ⟨i, hi, _, _, hd⟩ := (decreaseKey_ret q q' v key h).1
  rw [hd, (siftUp_perm _ _).size_eq, Array.size_set]

private lemma extraction_size {W : Type uprd1} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (h : (extractMin q).ret = some (entry, q')) :
    q'.heap.data.size + 1 = q.heap.data.size := by
  have hc := congrArg Multiset.card
    (MinHeap.extractMin_cons_elements (extractMin_ret q q' entry h).1)
  simpa [MinHeap.elements] using hc

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uprd2

private lemma scan_size {W : Type uprd2} [LinearOrder W] {n : Nat}
    (weight : Sym2 (Fin n) → W) (current : Fin n) (vs : List (Fin n))
    (state : State W n) :
    (scan weight current vs state).ret.queue.heap.data.size = state.queue.heap.data.size := by
  induction vs generalizing state with
  | nil => simp [scan]
  | cons v vs ih =>
    simp only [scan, TimeM.ret_bind]
    dsimp only [TimeM.bind, liftHeap]
    by_cases hlive : (Cslib.Algorithms.Lean.IndexedMinQueue.member state.queue v).ret = true
    · simp only [ite_eq_left hlive, TimeM.ret_bind]
      by_cases hlt : (weight (Sym2.mk current v) : WithTop W) < queueKey state.queue v
      · obtain ⟨q', hd⟩ := decrease_succeeds state.queue v
          (weight (Sym2.mk current v)) hlive hlt
        simp only [ite_eq_left hlt, TimeM.ret_bind, hd]
        exact (ih { state with queue := q', parent := state.parent.set v (some current) }).trans
          (decrease_size state.queue q' v (weight (Sym2.mk current v)) hd)
      · simpa only [ite_eq_right hlt] using ih state
    · simpa only [ite_eq_right hlive] using ih state

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uprd3

private lemma initQueue_size {W : Type uprd3} [LinearOrder W] [Zero W] {n : Nat}
    (root : Fin n) (vs : List (Fin n)) (q : IndexedMinQueue W n)
    (hn : vs.Nodup) (ha : ∀ v ∈ vs, q.position[v] = none) :
    (initQueue root vs q).ret.heap.data.size = q.heap.data.size + vs.length := by
  induction vs generalizing q with
  | nil => simp [initQueue]
  | cons v vs ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
    obtain ⟨q', hins⟩ := insert_succeeds q v
      (if v = root then (0 : W) else ⊤) (ha v (by simp))
    have habsent : ∀ w ∈ vs, q'.position[w] = none := by
      intro w hw
      have hwv : w ≠ v := by
        intro h
        subst w
        exact hnot hw
      have hflag := (insert_ret q q' v (if v = root then (0 : W) else ⊤) hins).2.2 w hwv
      rw [ha w (List.mem_cons_of_mem v hw)] at hflag
      cases hp' : q'.position[w] with
      | none => rfl
      | some i => simp [hp'] at hflag
    simp only [initQueue, TimeM.ret_bind, liftHeap, hins]
    rw [ih q' htail habsent, insert_size q q' v _ hins]
    simp only [List.length_cons]
    omega

private lemma vertices_length {n : Nat} (graph : DirectedAdjacency (Fin n)) :
    graph.vertices.length = n := by
  have hset : graph.vertices.toFinset = Finset.univ := by
    ext v
    simp [graph.vertices_complete v]
  rw [← List.toFinset_card_of_nodup graph.vertices_nodup, hset]
  simp

private lemma initial_size {W : Type uprd3} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (root : Fin n) :
    (initQueue (W := W) root graph.vertices (empty n)).ret.heap.data.size = n := by
  rw [initQueue_size root graph.vertices (empty n) graph.vertices_nodup
    (fun v _ => empty_position v), vertices_length graph]
  simp [empty, MinHeap.empty]

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uprd4

private lemma loop_drains {W : Type uprd4} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (fuel : Nat) (state : State W n) (hsize : state.queue.heap.data.size ≤ fuel) :
    (loop graph weight fuel state).ret.queue.heap.data.size = 0 := by
  induction fuel generalizing state with
  | zero => simpa [loop] using Nat.eq_zero_of_le_zero hsize
  | succ fuel ih =>
    cases hex : (extractMin state.queue).ret with
    | none =>
      have he := (extractMin_eq_none_iff state.queue).mp hex
      simpa only [loop, TimeM.ret_bind, liftHeap, hex, TimeM.ret_pure] using he
    | some pair =>
      rcases pair with ⟨entry, q'⟩
      let updated := (scan weight (ofLex entry).2 (graph.adjacency (ofLex entry).2)
        { state with queue := q', extracted := ofLex entry :: state.extracted }).ret
      have hs : updated.queue.heap.data.size ≤ fuel := by
        dsimp only [updated]
        rw [scan_size]
        change q'.heap.data.size ≤ fuel
        have he := extraction_size state.queue q' entry hex
        omega
      simp only [loop, TimeM.ret_bind, liftHeap, hex]
      exact ih updated hs

private lemma prim_queue_empty {W : Type uprd4} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    (worker graph weight root).ret.queue.heap.data.size = 0 := by
  simp only [worker, TimeM.ret_bind]
  apply loop_drains
  exact (initial_size graph root).le

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uinik4

private lemma initQueue_keys {W : Type uinik4} [LinearOrder W] [Zero W] {n : Nat}
    (root : Fin n) (vs : List (Fin n)) (q : IndexedMinQueue W n)
    (hn : vs.Nodup) (ha : ∀ v ∈ vs, q.position[v] = none)
    (hk : ∀ e ∈ q.heap.elements,
      (ofLex e).1 = if (ofLex e).2 = root then ((0 : W) : WithTop W) else ⊤) :
    ∀ e ∈ (initQueue root vs q).ret.heap.elements,
      (ofLex e).1 = if (ofLex e).2 = root then ((0 : W) : WithTop W) else ⊤ := by
  induction vs generalizing q with
  | nil => simpa [initQueue] using hk
  | cons v vs ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
    obtain ⟨q', hins⟩ := insert_succeeds q v
      (if v = root then ((0 : W) : WithTop W) else ⊤) (ha v (by simp))
    have hs := insert_ret q q' v (if v = root then ((0 : W) : WithTop W) else ⊤) hins
    have habsent : ∀ w ∈ vs, q'.position[w] = none := by
      intro w hw
      have hwv : w ≠ v := by
        intro h
        subst w
        exact hnot hw
      have hflag := hs.2.2 w hwv
      rw [ha w (List.mem_cons_of_mem v hw)] at hflag
      cases hp' : q'.position[w] with
      | none => rfl
      | some i => simp [hp'] at hflag
    have hk' : ∀ e ∈ q'.heap.elements,
        (ofLex e).1 = if (ofLex e).2 = root then ((0 : W) : WithTop W) else ⊤ := by
      intro e he
      rw [hs.1, MinHeap.elements_push] at he
      rcases Multiset.mem_cons.mp he with rfl | he
      · rfl
      · exact hk e he
    simpa only [initQueue, TimeM.ret_bind, liftHeap, hins] using ih q' htail habsent hk'

private lemma initial_queueKey {W : Type uinik4} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (root v : Fin n) :
    queueKey (initQueue (W := W) root graph.vertices (empty n)).ret v =
      if v = root then ((0 : W) : WithTop W) else ⊤ := by
  let q := (initQueue (W := W) root graph.vertices (empty n)).ret
  have hk := initQueue_keys (W := W) root graph.vertices (empty n) graph.vertices_nodup
    (fun w _ => empty_position w) (by simp [empty, MinHeap.empty, MinHeap.elements])
  have hp := initQueue_full (W := W) graph root v
  change q.position[v].isSome = true at hp
  cases hi : q.position[v] with
  | none => simp [hi] at hp
  | some i =>
    have hb := position_valid q v i hi
    have hid := (q.inverse v i).mp hi
    have he : q.heap.data[i.val]'hb ∈ q.heap.elements := by
      change q.heap.data[i.val]'hb ∈ q.heap.data.toList
      simp
    rw [queueKey_some q v i hi]
    have hv : (ofLex (q.heap.data[i.val]'hb)).2 = v := hid.choose_spec
    simpa only [hv] using hk _ he

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe upr1

private lemma extraction_key_le {W : Type upr1} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (hex : (extractMin q).ret = some (entry, q')) (v : Fin n) :
    (ofLex entry).1 ≤ queueKey q v := by
  cases hi : q.position[v] with
  | none =>
    unfold queueKey
    split
    · exact le_top
    · rename_i j hj
      cases hi.symm.trans hj
  | some i =>
    have hb := position_valid q v i hi
    have he : q.heap.data[i.val]'hb ∈ q.heap.elements := by
      change q.heap.data[i.val]'hb ∈ q.heap.data.toList
      simp
    rw [queueKey_some q v i hi]
    exact Prod.Lex.monotone_fst _ _
      (MinHeap.extractMin_le (extractMin_ret q q' entry hex).1 he)

private lemma scan_extracted {W : Type upr1} [LinearOrder W] {n : Nat}
    (weight : Sym2 (Fin n) → W) (current : Fin n) (vs : List (Fin n))
    (state : State W n) : (scan weight current vs state).ret.extracted = state.extracted := by
  induction vs generalizing state with
  | nil => simp [scan]
  | cons v vs ih =>
    simp only [scan, TimeM.ret_bind]
    dsimp only [TimeM.bind, liftHeap]
    by_cases hlive : (Cslib.Algorithms.Lean.IndexedMinQueue.member state.queue v).ret = true
    · simp only [ite_eq_left hlive, TimeM.ret_bind]
      by_cases hlt : (weight (Sym2.mk current v) : WithTop W) < queueKey state.queue v
      · obtain ⟨q', hd⟩ := decrease_succeeds state.queue v
          (weight (Sym2.mk current v)) hlive hlt
        simp only [ite_eq_left hlt, TimeM.ret_bind, hd]
        exact ih { state with queue := q', parent := state.parent.set v (some current) }
      · simpa only [ite_eq_right hlt] using ih state
    · simpa only [ite_eq_right hlive] using ih state

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe u

private lemma heap_entry_key {W : Type u} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (he : entry ∈ q.heap.elements) : queueKey q (ofLex entry).2 = (ofLex entry).1 := by
  change entry ∈ q.heap.data.toList at he
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp he
  have hb : j < q.heap.data.size := by simpa using hj
  have hentry : q.heap.data[j]'hb = entry := by simpa using he
  let i : Fin n := ⟨j, hb.trans_le q.capacity⟩
  have hp : q.position[(ofLex entry).2] = some i :=
    (q.inverse (ofLex entry).2 i).mpr ⟨hb, by simp only [i, hentry]⟩
  rw [queueKey_some q (ofLex entry).2 i hp]
  simp only [i, hentry]

private lemma decrease_entry_membership {W : Type u} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (v : Fin n) (key : W)
    (hd : (decreaseKey q v key).ret = some q') :
    toLex (((key : W) : WithTop W), v) ∈ q'.heap.elements ∧
      ∀ e ∈ q'.heap.elements,
        e = toLex (((key : W) : WithTop W), v) ∨ e ∈ q.heap.elements := by
  obtain ⟨i, hi, _, _, hdata⟩ := (decreaseKey_ret q q' v key hd).1
  let a := q.heap.data.set i.val (toLex (((key : W) : WithTop W), v)) hi
  have hperm := (siftUp_perm a i.val).toList
  constructor
  · change toLex (((key : W) : WithTop W), v) ∈ q'.heap.data.toList
    rw [hdata]
    apply hperm.mem_iff.mpr
    have hsize : i.val < a.size := by simpa only [a, Array.size_set] using hi
    apply List.mem_iff_getElem.mpr
    refine ⟨i.val, by simpa using hsize, ?_⟩
    simp [a]
  · intro e he
    change e ∈ q'.heap.data.toList at he
    rw [hdata] at he
    have hmem := hperm.mem_iff.mp he
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hmem
    have hb : j < q.heap.data.size := by
      simpa only [a, Array.length_toList, Array.size_set] using hj
    have he' : a[j]'(by simpa only [a, Array.size_set] using hb) = e := by simpa using he
    by_cases hij : i.val = j
    · left
      have hnew : a[j]'(by simpa only [a, Array.size_set] using hb) =
          toLex (((key : W) : WithTop W), v) := by simp [a, hij]
      exact he'.symm.trans hnew
    · right
      have hold : q.heap.data[j]'hb = e := by
        simpa only [a, Array.getElem_set, ite_eq_right hij] using he'
      change e ∈ q.heap.data.toList
      exact List.mem_iff_getElem.mpr ⟨j, by simpa using hb, by simpa using hold⟩

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe udk3

private lemma queueKey_none {W : Type udk3} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) (hp : q.position[v] = none) :
    queueKey q v = ⊤ := by
  unfold queueKey
  split
  · rfl
  · rename_i i hi
    cases hp.symm.trans hi

private lemma decrease_queueKeys {W : Type udk3} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (v : Fin n) (key : W)
    (hd : (decreaseKey q v key).ret = some q') :
    queueKey q' v = (key : WithTop W) ∧
      ∀ w : Fin n, w ≠ v → queueKey q' w = queueKey q w := by
  have hm := decrease_entry_membership q q' v key hd
  constructor
  · simpa using heap_entry_key q' (toLex ((key : WithTop W), v)) hm.1
  · intro w hwv
    cases hi : q'.position[w] with
    | none =>
      have hp := (decreaseKey_ret q q' v key hd).2 w
      cases ho : q.position[w] with
      | none => rw [queueKey_none q' w hi, queueKey_none q w ho]
      | some j => simp [hi, ho] at hp
    | some i =>
      have hb := position_valid q' w i hi
      let e := q'.heap.data[i.val]'hb
      have he : e ∈ q'.heap.elements := by
        change q'.heap.data[i.val]'hb ∈ q'.heap.data.toList
        simp
      have hid : (ofLex e).2 = w := (q'.inverse w i).mp hi |>.choose_spec
      have hkey' : queueKey q' w = (ofLex e).1 := queueKey_some q' w i hi
      have hold : e ∈ q.heap.elements := by
        rcases hm.2 e he with hnew | hold
        · rw [hnew] at hid
          change v = w at hid
          exact (hwv hid.symm).elim
        · exact hold
      have hkey := heap_entry_key q e hold
      rw [hid] at hkey
      exact hkey'.trans hkey.symm

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe usp6

private lemma scan_presence {W : Type usp6} [LinearOrder W] {n : Nat}
    (weight : Sym2 (Fin n) → W) (current : Fin n) (vs : List (Fin n))
    (state : State W n) (w : Fin n) :
    (scan weight current vs state).ret.queue.position[w].isSome =
      state.queue.position[w].isSome := by
  induction vs generalizing state with
  | nil => simp [scan]
  | cons v vs ih =>
    simp only [scan, TimeM.ret_bind]
    dsimp only [TimeM.bind, liftHeap]
    by_cases hlive : (Cslib.Algorithms.Lean.IndexedMinQueue.member state.queue v).ret = true
    · simp only [ite_eq_left hlive, TimeM.ret_bind]
      by_cases hlt : (weight (Sym2.mk current v) : WithTop W) < queueKey state.queue v
      · obtain ⟨q', hd⟩ := decrease_succeeds state.queue v
          (weight (Sym2.mk current v)) hlive hlt
        simp only [ite_eq_left hlt, TimeM.ret_bind, hd]
        exact (ih { state with queue := q', parent := state.parent.set v (some current) }).trans
          ((decreaseKey_ret state.queue q' v (weight (Sym2.mk current v)) hd).2 w)
      · simpa only [ite_eq_right hlt] using ih state
    · simpa only [ite_eq_right hlive] using ih state

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uep1

private lemma extraction_present {W : Type uep1} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (hex : (extractMin q).ret = some (entry, q')) :
    q.position[(ofLex entry).2].isSome = true := by
  have he := MinHeap.extractMin_mem (extractMin_ret q q' entry hex).1
  change entry ∈ q.heap.data.toList at he
  cases hp : q.position[(ofLex entry).2] with
  | none => exact False.elim ((position_eq_none_iff q (ofLex entry).2).mp hp ⟨entry, he, rfl⟩)
  | some i => rfl

private lemma extraction_cut_minimum {W : Type uep1} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (seen : List (Fin n)) (q q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (hex : (extractMin q).ret = some (entry, q'))
    (hb : ∀ u ∈ seen, ∀ w : Fin n, q.position[w].isSome = true →
      w ∈ graph.adjacency u → queueKey q w ≤ (weight (Sym2.mk u w) : WithTop W)) :
    ∀ u ∈ seen, ∀ w : Fin n, q.position[w].isSome = true →
      w ∈ graph.adjacency u → (ofLex entry).1 ≤ (weight (Sym2.mk u w) : WithTop W) := by
  intro u hu w hp hadj
  exact (extraction_key_le q q' entry hex w).trans (hb u hu w hp hadj)

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe ueqk1

private lemma extraction_queueKeys {W : Type ueqk1} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (hex : (extractMin q).ret = some (entry, q')) (w : Fin n)
    (hw : w ≠ (ofLex entry).2) : queueKey q' w = queueKey q w := by
  have hr := extractMin_ret q q' entry hex
  cases hi : q'.position[w] with
  | none =>
    have hp := hr.2.2 w hw
    cases ho : q.position[w] with
    | none => rw [queueKey_none q' w hi, queueKey_none q w ho]
    | some j => simp [hi, ho] at hp
  | some i =>
    have hb := position_valid q' w i hi
    let e := q'.heap.data[i.val]'hb
    have he : e ∈ q'.heap.elements := by
      change q'.heap.data[i.val]'hb ∈ q'.heap.data.toList
      simp
    have hid : (ofLex e).2 = w := (q'.inverse w i).mp hi |>.choose_spec
    have hne : e ≠ entry := by
      intro heq
      rw [heq] at hid
      exact hw hid.symm
    have hold : e ∈ q.heap.elements := (MinHeap.extractMin_mem_of_ne_iff hr.1 hne).mp he
    have hkey := heap_entry_key q e hold
    rw [hid] at hkey
    exact (queueKey_some q' w i hi).trans hkey.symm

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uec1

private lemma extraction_presence_iff {W : Type uec1} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (hex : (extractMin q).ret = some (entry, q')) (w : Fin n) :
    q'.position[w].isSome = true ↔ w ≠ (ofLex entry).2 ∧ q.position[w].isSome = true := by
  have hr := extractMin_ret q q' entry hex
  by_cases hw : w = (ofLex entry).2
  · subst w
    simp [hr.2.1]
  · constructor
    · intro hp
      exact ⟨hw, (hr.2.2 w hw).symm.trans hp⟩
    · intro hp
      exact (hr.2.2 w hw).trans hp.2

private lemma extracted_step_complement {W : Type uec1} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (state : State W n) (q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (hex : (extractMin state.queue).ret = some (entry, q'))
    (hc : ∀ w : Fin n, state.queue.position[w].isSome = true ↔
      w ∉ state.extracted.map Prod.snd) :
    ∀ w : Fin n,
      (scan weight (ofLex entry).2 (graph.adjacency (ofLex entry).2)
        { state with
          queue := q'
          extracted := ofLex entry :: state.extracted }).ret.queue.position[w].isSome = true ↔
      w ∉ (ofLex entry :: state.extracted).map Prod.snd := by
  intro w
  rw [scan_presence, extraction_presence_iff state.queue q' entry hex w, hc w]
  simp only [List.map_cons, List.mem_cons, not_or]

private lemma extracted_step_nodup {W : Type uec1} [LinearOrder W] {n : Nat}
    (state : State W n) (q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (hex : (extractMin state.queue).ret = some (entry, q'))
    (hn : (state.extracted.map Prod.snd).Nodup)
    (hc : ∀ w : Fin n, state.queue.position[w].isSome = true ↔
      w ∉ state.extracted.map Prod.snd) :
    ((ofLex entry :: state.extracted).map Prod.snd).Nodup := by
  apply List.nodup_cons.mpr
  exact ⟨(hc (ofLex entry).2).mp (extraction_present state.queue q' entry hex), hn⟩

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uskm1

private lemma scan_key_le {W : Type uskm1} [LinearOrder W] {n : Nat}
    (weight : Sym2 (Fin n) → W) (current : Fin n) (vs : List (Fin n))
    (state : State W n) (w : Fin n) :
    queueKey (scan weight current vs state).ret.queue w ≤ queueKey state.queue w := by
  induction vs generalizing state with
  | nil => simp [scan]
  | cons v vs ih =>
    simp only [scan, TimeM.ret_bind]
    dsimp only [TimeM.bind, liftHeap]
    by_cases hlive : (Cslib.Algorithms.Lean.IndexedMinQueue.member state.queue v).ret = true
    · simp only [ite_eq_left hlive, TimeM.ret_bind]
      by_cases hlt : (weight (Sym2.mk current v) : WithTop W) < queueKey state.queue v
      · obtain ⟨q', hd⟩ := decrease_succeeds state.queue v
          (weight (Sym2.mk current v)) hlive hlt
        simp only [ite_eq_left hlt, TimeM.ret_bind, hd]
        have hk := decrease_queueKeys state.queue q' v (weight (Sym2.mk current v)) hd
        apply (ih { state with queue := q', parent := state.parent.set v (some current) }).trans
        by_cases hwv : w = v
        · subst w
          rw [hk.1]
          exact hlt.le
        · exact (hk.2 w hwv).le
      · simpa only [ite_eq_right hlt] using ih state
    · simpa only [ite_eq_right hlive] using ih state

private lemma scan_tests_le {W : Type uskm1} [LinearOrder W] {n : Nat}
    (weight : Sym2 (Fin n) → W) (current : Fin n) (vs : List (Fin n))
    (state : State W n) : (scan weight current vs state).time.2.2 ≤ vs.length := by
  induction vs generalizing state with
  | nil => simp [scan]
  | cons v vs ih =>
    by_cases hlive : (Cslib.Algorithms.Lean.IndexedMinQueue.member state.queue v).ret = true
    · by_cases hlt : (weight (Sym2.mk current v) : WithTop W) < queueKey state.queue v
      · obtain ⟨q', hd⟩ := decrease_succeeds state.queue v
          (weight (Sym2.mk current v)) hlive hlt
        simpa [scan, TimeM.bind, liftHeap, hlive, hlt, hd, Nat.add_comm] using
          Nat.succ_le_succ
            (ih { state with queue := q', parent := state.parent.set v (some current) })
      · simpa [scan, TimeM.bind, liftHeap, hlive, hlt, Nat.add_comm] using
          Nat.succ_le_succ (ih state)
    · simpa [scan, TimeM.bind, liftHeap, hlive, Nat.add_comm] using
        (ih state).trans (Nat.le_succ vs.length)

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uske1

private lemma scan_key_le_edge {W : Type uske1} [LinearOrder W] {n : Nat}
    (weight : Sym2 (Fin n) → W) (current : Fin n) (vs : List (Fin n))
    (state : State W n) (w : Fin n) (hm : w ∈ vs)
    (hp : state.queue.position[w].isSome = true) :
    queueKey (scan weight current vs state).ret.queue w ≤
      (weight (Sym2.mk current w) : WithTop W) := by
  induction vs generalizing state with
  | nil => simp at hm
  | cons v vs ih =>
    simp only [scan, TimeM.ret_bind]
    dsimp only [TimeM.bind, liftHeap]
    by_cases hlive : (Cslib.Algorithms.Lean.IndexedMinQueue.member state.queue v).ret = true
    · simp only [ite_eq_left hlive, TimeM.ret_bind]
      by_cases hlt : (weight (Sym2.mk current v) : WithTop W) < queueKey state.queue v
      · obtain ⟨q', hd⟩ := decrease_succeeds state.queue v
          (weight (Sym2.mk current v)) hlive hlt
        simp only [ite_eq_left hlt, TimeM.ret_bind, hd]
        by_cases hwv : w = v
        · subst w
          have ht := scan_key_le weight current vs
            { state with queue := q', parent := state.parent.set v (some current) } v
          simpa only [(decrease_queueKeys state.queue q' v (weight (Sym2.mk current v)) hd).1]
            using ht
        · have hm' : w ∈ vs := by simpa [hwv] using hm
          have hp' : q'.position[w].isSome = true :=
            ((decreaseKey_ret state.queue q' v (weight (Sym2.mk current v)) hd).2 w).trans hp
          exact ih { state with queue := q', parent := state.parent.set v (some current) } hm' hp'
      · simp only [ite_eq_right hlt]
        by_cases hwv : w = v
        · subst w
          exact (scan_key_le weight current vs state v).trans (le_of_not_gt hlt)
        · exact ih state (by simpa [hwv] using hm) hp
    · have hwv : w ≠ v := by
        intro he
        subst w
        exact hlive ((member_ret state.queue v).trans hp)
      simpa only [ite_eq_right hlive] using ih state (by simpa [hwv] using hm) hp

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uscb1

private lemma scan_cut_bounds {W : Type uscb1} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (current : Fin n) (seen : List (Fin n)) (state : State W n)
    (hprev : ∀ u ∈ seen, ∀ w : Fin n, state.queue.position[w].isSome = true →
      w ∈ graph.adjacency u → queueKey state.queue w ≤ (weight (Sym2.mk u w) : WithTop W)) :
    ∀ u ∈ current :: seen, ∀ w : Fin n,
      (scan weight current (graph.adjacency current) state).ret.queue.position[w].isSome = true →
      w ∈ graph.adjacency u →
      queueKey (scan weight current (graph.adjacency current) state).ret.queue w ≤
        (weight (Sym2.mk u w) : WithTop W) := by
  intro u hu w hp hadj
  have hpold : state.queue.position[w].isSome = true :=
    (scan_presence weight current (graph.adjacency current) state w).symm.trans hp
  rcases List.mem_cons.mp hu with huc | hus
  · subst u
    exact scan_key_le_edge weight current (graph.adjacency current) state w hadj hpold
  · exact (scan_key_le weight current (graph.adjacency current) state w).trans
      (hprev u hus w hpold hadj)

private lemma extraction_cut_bounds {W : Type uscb1} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (seen : List (Fin n)) (q q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (hex : (extractMin q).ret = some (entry, q'))
    (hprev : ∀ u ∈ seen, ∀ w : Fin n, q.position[w].isSome = true →
      w ∈ graph.adjacency u → queueKey q w ≤ (weight (Sym2.mk u w) : WithTop W)) :
    ∀ u ∈ seen, ∀ w : Fin n, q'.position[w].isSome = true →
      w ∈ graph.adjacency u → queueKey q' w ≤ (weight (Sym2.mk u w) : WithTop W) := by
  intro u hu w hp hadj
  have hr := extractMin_ret q q' entry hex
  have hw : w ≠ (ofLex entry).2 := by
    intro he
    subst w
    simp [hr.2.1] at hp
  have hpold : q.position[w].isSome = true := (hr.2.2 w hw).symm.trans hp
  rw [extraction_queueKeys q q' entry hex w hw]
  exact hprev u hu w hpold hadj

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe ulp1

private lemma loop_trace_partition {W : Type ulp1} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (fuel : Nat) (state : State W n)
    (hn : (state.extracted.map Prod.snd).Nodup)
    (hc : ∀ w : Fin n, state.queue.position[w].isSome = true ↔
      w ∉ state.extracted.map Prod.snd) :
    ((loop graph weight fuel state).ret.extracted.map Prod.snd).Nodup ∧
      ∀ w : Fin n, (loop graph weight fuel state).ret.queue.position[w].isSome = true ↔
        w ∉ (loop graph weight fuel state).ret.extracted.map Prod.snd := by
  induction fuel generalizing state with
  | zero => simpa [loop] using And.intro hn hc
  | succ fuel ih =>
    cases hex : (extractMin state.queue).ret with
    | none =>
      simpa only [loop, TimeM.ret_bind, liftHeap, hex, TimeM.ret_pure] using And.intro hn hc
    | some pair =>
      rcases pair with ⟨entry, q'⟩
      let updated := (scan weight (ofLex entry).2 (graph.adjacency (ofLex entry).2)
        { state with queue := q', extracted := ofLex entry :: state.extracted }).ret
      have hx : updated.extracted = ofLex entry :: state.extracted :=
        scan_extracted weight _ _ _
      have hn' : (updated.extracted.map Prod.snd).Nodup := by
        rw [hx]
        exact extracted_step_nodup state q' entry hex hn hc
      have hc' : ∀ w : Fin n, updated.queue.position[w].isSome = true ↔
          w ∉ updated.extracted.map Prod.snd := by
        intro w
        rw [hx]
        exact extracted_step_complement graph weight state q' entry hex hc w
      simpa only [loop, TimeM.ret_bind, liftHeap, hex] using ih updated hn' hc'

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe upcov1

private lemma prim_partition {W : Type upcov1} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    ((worker graph weight root).ret.extracted.map Prod.snd).Nodup ∧
      ∀ w : Fin n, (worker graph weight root).ret.queue.position[w].isSome = true ↔
        w ∉ (worker graph weight root).ret.extracted.map Prod.snd := by
  let q := (initQueue (W := W) root graph.vertices (empty n)).ret
  let state : State W n := ⟨q, Vector.replicate n none, []⟩
  have hc : ∀ w : Fin n, state.queue.position[w].isSome = true ↔
      w ∉ state.extracted.map Prod.snd := by
    intro w
    simpa [state, q] using initQueue_full (W := W) graph root w
  have hn : (state.extracted.map Prod.snd).Nodup := by simp [state]
  simpa only [worker, TimeM.ret_bind, TimeM.ret_pure, q, state] using
    loop_trace_partition graph weight n state hn hc

private lemma prim_extracted_once {W : Type upcov1} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    ((worker graph weight root).ret.extracted.map Prod.snd).Nodup ∧
      ∀ w : Fin n, w ∈ (worker graph weight root).ret.extracted.map Prod.snd := by
  have hp := prim_partition graph weight root
  refine ⟨hp.1, ?_⟩
  intro w
  by_contra hm
  have hw := (hp.2 w).mpr hm
  cases hi : (worker graph weight root).ret.queue.position[w] with
  | none => simp [hi] at hw
  | some i =>
    have hb := position_valid (worker graph weight root).ret.queue w i hi
    rw [prim_queue_empty graph weight root] at hb
    omega

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uier1

private lemma initial_extract_root {W : Type uier1} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (root : Fin n) :
    ∃ q', (extractMin (initQueue (W := W) root graph.vertices (empty n)).ret).ret =
      some (toLex (((0 : W) : WithTop W), root), q') := by
  let q := (initQueue (W := W) root graph.vertices (empty n)).ret
  cases hex : (extractMin q).ret with
  | none =>
    have he := (extractMin_eq_none_iff q).mp hex
    have hs : q.heap.data.size = n := initial_size graph root
    have hn := root.isLt
    omega
  | some pair =>
    rcases pair with ⟨entry, q'⟩
    have hmin := extraction_key_le q q' entry hex root
    rw [initial_queueKey graph root root] at hmin
    rw [ite_eq_left rfl] at hmin
    have he := MinHeap.extractMin_mem (extractMin_ret q q' entry hex).1
    have hk := initQueue_keys (W := W) root graph.vertices (empty n) graph.vertices_nodup
      (fun v _ => empty_position v) (by simp [empty, MinHeap.empty, MinHeap.elements]) entry he
    have hid : (ofLex entry).2 = root := by
      by_contra hn
      rw [ite_eq_right hn] at hk
      rw [hk] at hmin
      simp at hmin
    rw [ite_eq_left hid] at hk
    have hp : entry = toLex (((0 : W) : WithTop W), root) := by
      apply ofLex.injective
      exact Prod.ext hk hid
    subst entry
    exact ⟨q', rfl⟩

end Cslib.Algorithms.Lean.Prim
