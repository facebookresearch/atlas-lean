/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.Prim.Basic
import all CSLibExt.Algorithms.Lean.Graph.Prim.QueueInvariants
import CSLibExt.Algorithms.Lean.DataStructures.IndexedMinQueue
import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency
import Cslib.Algorithms.Lean.TimeM
import Mathlib.Data.Sym.Sym2

/-!
# Prim parent and extraction-history invariants

Adapted from CLRS, fourth edition, section 21.2, Prim's algorithm.
Proofs and executable code authored with Codex under Adam Kiezun's authorization.
-/

open Cslib.Algorithms.Lean

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe usap2

private lemma scan_absent_parent {W : Type usap2} [LinearOrder W] {n : Nat}
    (weight : Sym2 (Fin n) → W) (current : Fin n) (vs : List (Fin n))
    (state : State W n) (w : Fin n) (habs : state.queue.position[w] = none) :
    (scan weight current vs state).ret.parent[w] = state.parent[w] := by
  induction vs generalizing state with
  | nil => simp [scan]
  | cons v vs ih =>
    simp only [scan, TimeM.ret_bind]
    dsimp only [TimeM.bind, liftHeap]
    by_cases hlive : (Cslib.Algorithms.Lean.IndexedMinQueue.member state.queue v).ret = true
    · simp only [ite_eq_left hlive, TimeM.ret_bind]
      have hwv : w ≠ v := by
        intro h
        subst w
        simp [member_ret, habs] at hlive
      by_cases hlt : (weight (Sym2.mk current v) : WithTop W) < queueKey state.queue v
      · obtain ⟨q', hd⟩ := decrease_succeeds state.queue v
          (weight (Sym2.mk current v)) hlive hlt
        have habs' : q'.position[w] = none := by
          have hp := (decreaseKey_ret state.queue q' v (weight (Sym2.mk current v)) hd).2 w
          rw [habs] at hp
          cases hq : q'.position[w] with
          | none => rfl
          | some i => simp [hq] at hp
        simp only [ite_eq_left hlt, TimeM.ret_bind, hd]
        rw [ih { state with queue := q', parent := state.parent.set v (some current) } habs']
        change (state.parent.set v.val (some current) v.isLt)[w.val] = state.parent[w.val]
        have hval : v.val ≠ w.val := fun h => hwv (Fin.ext h.symm)
        simp only [Vector.getElem_set, ite_eq_right hval]
      · simpa only [ite_eq_right hlt] using ih state habs
    · simpa only [ite_eq_right hlive] using ih state habs

private lemma extraction_absent {W : Type usap2} [LinearOrder W] {n : Nat}
    (q q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (hex : (extractMin q).ret = some (entry, q')) (v : Fin n)
    (habs : q.position[v] = none) : q'.position[v] = none := by
  have hs := extractMin_ret q q' entry hex
  by_cases he : v = (ofLex entry).2
  · simpa only [he] using hs.2.1
  · have hp := hs.2.2 v he
    rw [habs] at hp
    cases hv : q'.position[v] with
    | none => rfl
    | some i => simp [hv] at hp

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uphist1

private def parentHistory {n : Nat} (parents : Vector (Option (Fin n)) n)
    (seen : List (Fin n)) : Prop :=
  ∀ v p : Fin n, v ∈ seen → parents[v] = some p →
    ∃ before after : List (Fin n), seen = before ++ v :: after ∧ p ∈ after

private lemma position_none_of_seen {W : Type uphist1} [LinearOrder W] {n : Nat}
    (state : State W n)
    (hc : ∀ w : Fin n, state.queue.position[w].isSome = true ↔
      w ∉ state.extracted.map Prod.snd) (v : Fin n)
    (hv : v ∈ state.extracted.map Prod.snd) : state.queue.position[v] = none := by
  cases hi : state.queue.position[v] with
  | none => rfl
  | some i =>
    have hn := (hc v).mp (by simp [hi])
    exact False.elim (hn hv)

private lemma extracted_parent_history {W : Type uphist1} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (state : State W n) (q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (hex : (extractMin state.queue).ret = some (entry, q'))
    (hc : ∀ w : Fin n, state.queue.position[w].isSome = true ↔
      w ∉ state.extracted.map Prod.snd)
    (hp : ∀ w p : Fin n, state.parent[w] = some p → p ∈ state.extracted.map Prod.snd)
    (hh : parentHistory state.parent (state.extracted.map Prod.snd)) :
    parentHistory
      (scan weight (ofLex entry).2 (graph.adjacency (ofLex entry).2)
        { state with queue := q', extracted := ofLex entry :: state.extracted }).ret.parent
      ((ofLex entry).2 :: state.extracted.map Prod.snd) := by
  let start := { state with queue := q', extracted := ofLex entry :: state.extracted }
  intro v p hv hparent
  by_cases he : v = (ofLex entry).2
  · subst v
    have habs := (extractMin_ret state.queue q' entry hex).2.1
    have hf := scan_absent_parent weight (ofLex entry).2 (graph.adjacency (ofLex entry).2)
      start (ofLex entry).2 habs
    rw [hf] at hparent
    exact ⟨[], state.extracted.map Prod.snd, rfl, hp _ _ hparent⟩
  · have hvold : v ∈ state.extracted.map Prod.snd :=
      (List.mem_cons.mp hv).resolve_left he
    have habs := extraction_absent state.queue q' entry hex v
      (position_none_of_seen state hc v hvold)
    have hf := scan_absent_parent weight (ofLex entry).2 (graph.adjacency (ofLex entry).2)
      start v habs
    rw [hf] at hparent
    obtain ⟨before, after, hsplit, hpmem⟩ := hh v p hvold hparent
    exact ⟨(ofLex entry).2 :: before, after, by simp only [List.cons_append, hsplit], hpmem⟩

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe usps1

private lemma set_parent_seen {W : Type usps1} [LinearOrder W] {n : Nat}
    (state : State W n) (v current : Fin n) (seen : List (Fin n))
    (hp : ∀ (w p : Fin n), state.parent[w] = some p → p ∈ seen) :
    ∀ (w p : Fin n), (state.parent.set v (some current))[w] = some p → p ∈ current :: seen := by
  intro w p hw
  change (state.parent.set v.val (some current) v.isLt)[w.val] = some p at hw
  by_cases he : w = v
  · subst w
    simp only [Vector.getElem_set] at hw
    have hc : current = p := Option.some.inj hw
    simp [← hc]
  · have hval : v.val ≠ w.val := fun h => he (Fin.ext h.symm)
    simp only [Vector.getElem_set, ite_eq_right hval] at hw
    exact List.mem_cons_of_mem current (hp w p hw)

private lemma scan_parent_seen {W : Type usps1} [LinearOrder W] {n : Nat}
    (weight : Sym2 (Fin n) → W) (current : Fin n) (vs : List (Fin n))
    (state : State W n) (seen : List (Fin n))
    (hp : ∀ (w p : Fin n), state.parent[w] = some p → p ∈ current :: seen) :
    ∀ (w p : Fin n), (scan weight current vs state).ret.parent[w] = some p →
      p ∈ current :: seen := by
  induction vs generalizing state with
  | nil => simpa [scan] using hp
  | cons v vs ih =>
    simp only [scan, TimeM.ret_bind]
    dsimp only [TimeM.bind, liftHeap]
    by_cases hlive : (Cslib.Algorithms.Lean.IndexedMinQueue.member state.queue v).ret = true
    · simp only [ite_eq_left hlive, TimeM.ret_bind]
      by_cases hlt : (weight (Sym2.mk current v) : WithTop W) < queueKey state.queue v
      · obtain ⟨q', hd⟩ := decrease_succeeds state.queue v
          (weight (Sym2.mk current v)) hlive hlt
        simp only [ite_eq_left hlt, TimeM.ret_bind, hd]
        apply ih { state with queue := q', parent := state.parent.set v (some current) }
        intro w p hwp
        have hs := set_parent_seen state v current (current :: seen) hp w p hwp
        simpa only [List.mem_cons, or_self_left] using hs
      · simpa only [ite_eq_right hlt] using ih state hp
    · simpa only [ite_eq_right hlive] using ih state hp

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe ulph1

private lemma loop_parent_history {W : Type ulph1} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (fuel : Nat) (state : State W n)
    (hc : ∀ w : Fin n, state.queue.position[w].isSome = true ↔
      w ∉ state.extracted.map Prod.snd)
    (hp : ∀ w p : Fin n, state.parent[w] = some p → p ∈ state.extracted.map Prod.snd)
    (hh : parentHistory state.parent (state.extracted.map Prod.snd)) :
    parentHistory (loop graph weight fuel state).ret.parent
      ((loop graph weight fuel state).ret.extracted.map Prod.snd) := by
  induction fuel generalizing state with
  | zero => simpa [loop] using hh
  | succ fuel ih =>
    cases hex : (extractMin state.queue).ret with
    | none => simpa only [loop, TimeM.ret_bind, liftHeap, hex, TimeM.ret_pure] using hh
    | some pair =>
      rcases pair with ⟨entry, q'⟩
      let start := { state with queue := q', extracted := ofLex entry :: state.extracted }
      let updated := (scan weight (ofLex entry).2 (graph.adjacency (ofLex entry).2) start).ret
      have hx : updated.extracted = ofLex entry :: state.extracted :=
        scan_extracted weight _ _ _
      have hucomp : ∀ w : Fin n, updated.queue.position[w].isSome = true ↔
          w ∉ updated.extracted.map Prod.snd := by
        rw [hx]
        exact extracted_step_complement graph weight state q' entry hex hc
      have hstart : ∀ w p : Fin n, start.parent[w] = some p →
          p ∈ (ofLex entry).2 :: state.extracted.map Prod.snd := by
        intro w p hw
        exact List.mem_cons_of_mem _ (hp w p hw)
      have hup : ∀ w p : Fin n, updated.parent[w] = some p →
          p ∈ updated.extracted.map Prod.snd := by
        rw [hx, List.map_cons]
        exact scan_parent_seen weight (ofLex entry).2 (graph.adjacency (ofLex entry).2)
          start (state.extracted.map Prod.snd) hstart
      have huh : parentHistory updated.parent (updated.extracted.map Prod.snd) := by
        rw [hx, List.map_cons]
        exact extracted_parent_history graph weight state q' entry hex hc hp hh
      simpa only [loop, TimeM.ret_bind, liftHeap, hex] using ih updated hucomp hup huh

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe upph1

private lemma prim_parent_history {W : Type upph1} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    parentHistory (worker graph weight root).ret.parent
      ((worker graph weight root).ret.extracted.map Prod.snd) := by
  simp only [worker, TimeM.ret_bind]
  apply loop_parent_history
  · intro w
    simpa using initQueue_full (W := W) graph root w
  · intro w p hp
    simp at hp
  · intro v p hv
    simp at hv

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

universe uphr1

private lemma history_rank {n : Nat} (parents : Vector (Option (Fin n)) n)
    (seen : List (Fin n)) (hn : seen.Nodup) (hh : parentHistory parents seen)
    (v p : Fin n) (hv : v ∈ seen) (hp : parents[v] = some p) :
    seen.length - seen.idxOf p < seen.length - seen.idxOf v := by
  obtain ⟨before, after, heq, hpmem⟩ := hh v p hv hp
  have hn' : (before ++ v :: after).Nodup := heq ▸ hn
  have hparts := List.nodup_append.mp hn'
  have hvnot : v ∉ before := by
    intro hmem
    exact (hparts.2.2 v hmem v (by simp)) rfl
  have hpnot : p ∉ before := by
    intro hmem
    exact (hparts.2.2 p hmem p (List.mem_cons_of_mem v hpmem)) rfl
  have hvp : v ≠ p := by
    intro h
    subst p
    exact (List.nodup_cons.mp hparts.2.1).1 hpmem
  have hindex : seen.idxOf v < seen.idxOf p := by
    rw [heq, List.idxOf_append_of_notMem hvnot, List.idxOf_append_of_notMem hpnot,
      List.idxOf_cons_self, List.idxOf_cons_ne after hvp]
    omega
  have hpseen : p ∈ seen := by
    rw [heq]
    exact List.mem_append_right before (List.mem_cons_of_mem v hpmem)
  have hbound := List.idxOf_lt_length_of_mem hpseen
  omega

private lemma prim_parent_rank {W : Type uphr1} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n)
    (v p : Fin n) (hp : (worker graph weight root).ret.parent[v] = some p) :
    (worker graph weight root).ret.extracted.length -
        ((worker graph weight root).ret.extracted.map Prod.snd).idxOf p <
      (worker graph weight root).ret.extracted.length -
        ((worker graph weight root).ret.extracted.map Prod.snd).idxOf v := by
  have h := prim_extracted_once graph weight root
  have hh := prim_parent_history graph weight root
  simpa only [List.length_map] using
    history_rank _ _ h.1 hh v p (h.2 v) hp

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe usnk1

private lemma set_parent_none_key {W : Type usnk1} [LinearOrder W] {n : Nat}
    (weight : Sym2 (Fin n) → W) (state : State W n) (q' : IndexedMinQueue W n)
    (root v current : Fin n)
    (hd : (decreaseKey state.queue v (weight (Sym2.mk current v))).ret = some q')
    (hp : ∀ w : Fin n, w ≠ root → state.queue.position[w].isSome = true →
      state.parent[w] = none → queueKey state.queue w = ⊤) :
    ∀ w : Fin n, w ≠ root → q'.position[w].isSome = true →
      (state.parent.set v (some current))[w] = none → queueKey q' w = ⊤ := by
  intro w hwroot hw hparent
  change (state.parent.set v.val (some current) v.isLt)[w.val] = none at hparent
  by_cases he : w = v
  · subst w
    simp only [Vector.getElem_set] at hparent
    cases hparent
  · have hval : v.val ≠ w.val := fun h => he (Fin.ext h.symm)
    simp only [Vector.getElem_set, ite_eq_right hval] at hparent
    have hold :=
      ((decreaseKey_ret state.queue q' v (weight (Sym2.mk current v)) hd).2 w).symm.trans hw
    exact ((decrease_queueKeys state.queue q' v (weight (Sym2.mk current v)) hd).2 w he).trans
      (hp w hwroot hold hparent)

private lemma scan_none_key {W : Type usnk1} [LinearOrder W] {n : Nat}
    (weight : Sym2 (Fin n) → W) (root current : Fin n) (vs : List (Fin n))
    (state : State W n)
    (hp : ∀ w : Fin n, w ≠ root → state.queue.position[w].isSome = true →
      state.parent[w] = none → queueKey state.queue w = ⊤) :
    ∀ w : Fin n, w ≠ root → (scan weight current vs state).ret.queue.position[w].isSome = true →
      (scan weight current vs state).ret.parent[w] = none →
        queueKey (scan weight current vs state).ret.queue w = ⊤ := by
  induction vs generalizing state with
  | nil => simpa [scan] using hp
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
          (set_parent_none_key weight state q' root v current hd hp)
      · simpa only [ite_eq_right hlt] using ih state hp
    · simpa only [ite_eq_right hlive] using ih state hp

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe ulnk1

private lemma loop_none_key {W : Type ulnk1} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (root : Fin n) (fuel : Nat) (state : State W n)
    (hp : ∀ w : Fin n, w ≠ root → state.queue.position[w].isSome = true →
      state.parent[w] = none → queueKey state.queue w = ⊤) :
    ∀ w : Fin n, w ≠ root → (loop graph weight fuel state).ret.queue.position[w].isSome = true →
      (loop graph weight fuel state).ret.parent[w] = none →
        queueKey (loop graph weight fuel state).ret.queue w = ⊤ := by
  induction fuel generalizing state with
  | zero => simpa [loop] using hp
  | succ fuel ih =>
    cases hex : (extractMin state.queue).ret with
    | none => simpa only [loop, TimeM.ret_bind, liftHeap, hex, TimeM.ret_pure] using hp
    | some pair =>
      rcases pair with ⟨entry, q'⟩
      let start := { state with queue := q', extracted := ofLex entry :: state.extracted }
      have hs : ∀ w : Fin n, w ≠ root → start.queue.position[w].isSome = true →
          start.parent[w] = none → queueKey start.queue w = ⊤ := by
        intro w hroot hw hparent
        obtain ⟨hne, hold⟩ := (extraction_presence_iff state.queue q' entry hex w).mp hw
        exact (extraction_queueKeys state.queue q' entry hex w hne).trans
          (hp w hroot hold hparent)
      have hu := scan_none_key weight root (ofLex entry).2 (graph.adjacency (ofLex entry).2)
        start hs
      simpa only [loop, TimeM.ret_bind, liftHeap, hex] using ih
        (scan weight (ofLex entry).2 (graph.adjacency (ofLex entry).2) start).ret hu

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uepe1

private lemma extraction_parent_exists {W : Type uepe1} [LinearOrder W] {n : Nat}
    (state : State W n) (root : Fin n) (entry : WithTop W ×ₗ Fin n)
    (q' : IndexedMinQueue W n) (hex : (extractMin state.queue).ret = some (entry, q'))
    (hne : (ofLex entry).2 ≠ root) (hfinite : (ofLex entry).1 ≠ ⊤)
    (hp : ∀ w : Fin n, w ≠ root → state.queue.position[w].isSome = true →
      state.parent[w] = none → queueKey state.queue w = ⊤) :
    ∃ p : Fin n, state.parent[(ofLex entry).2] = some p := by
  have hmem := MinHeap.extractMin_mem (extractMin_ret state.queue q' entry hex).1
  have hkey := heap_entry_key state.queue entry hmem
  cases hparent : state.parent[(ofLex entry).2] with
  | none =>
    have hk := hp (ofLex entry).2 hne (extraction_present state.queue q' entry hex) hparent
    exact False.elim (hfinite (hkey.symm.trans hk))
  | some p => exact ⟨p, rfl⟩

private lemma extraction_parent_in_seen {W : Type uepe1} [LinearOrder W] {n : Nat}
    (state : State W n) (root : Fin n) (entry : WithTop W ×ₗ Fin n)
    (q' : IndexedMinQueue W n) (hex : (extractMin state.queue).ret = some (entry, q'))
    (hne : (ofLex entry).2 ≠ root) (hfinite : (ofLex entry).1 ≠ ⊤)
    (hp : ∀ w : Fin n, w ≠ root → state.queue.position[w].isSome = true →
      state.parent[w] = none → queueKey state.queue w = ⊤)
    (hseen : ∀ (w p : Fin n), state.parent[w] = some p →
      p ∈ state.extracted.map Prod.snd) :
    ∃ p : Fin n, p ∈ state.extracted.map Prod.snd ∧ state.parent[(ofLex entry).2] = some p := by
  obtain ⟨p, hparent⟩ := extraction_parent_exists state root entry q' hex hne hfinite hp
  exact ⟨p, hseen _ _ hparent, hparent⟩

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe u

private lemma loop_absent_parent {W : Type u} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (fuel : Nat) (state : State W n) (w : Fin n) (habs : state.queue.position[w] = none) :
    (loop graph weight fuel state).ret.parent[w] = state.parent[w] := by
  induction fuel generalizing state with
  | zero => simp [loop]
  | succ fuel ih =>
    cases hex : (extractMin state.queue).ret with
    | none => simp only [loop, TimeM.ret_bind, liftHeap, hex, TimeM.ret_pure]
    | some pair =>
      rcases pair with ⟨entry, q'⟩
      let extracted : State W n :=
        { state with queue := q', extracted := ofLex entry :: state.extracted }
      let updated := (scan weight (ofLex entry).2 (graph.adjacency (ofLex entry).2) extracted).ret
      have habs' := extraction_absent state.queue q' entry hex w habs
      have hu : updated.queue.position[w] = none := by
        have hp := scan_presence weight (ofLex entry).2
          (graph.adjacency (ofLex entry).2) extracted w
        change updated.queue.position[w].isSome = q'.position[w].isSome at hp
        rw [habs'] at hp
        cases hw : updated.queue.position[w] with
        | none => rfl
        | some i => simp [hw] at hp
      simp only [loop, TimeM.ret_bind, liftHeap, hex]
      rw [ih updated hu]
      exact scan_absent_parent weight _ _ extracted w habs'

private lemma prim_root_parent {W : Type u} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    (worker graph weight root).ret.parent[root] = none := by
  cases n with
  | zero => exact Fin.elim0 root
  | succ k =>
    let q := (initQueue (W := W) root graph.vertices (empty (k + 1))).ret
    obtain ⟨q', hex⟩ := initial_extract_root (W := W) graph root
    have habs : q'.position[root] = none :=
      (extractMin_ret q q' (toLex (((0 : W) : WithTop W), root)) hex).2.1
    let extracted : State W (k + 1) :=
      ⟨q', Vector.replicate (k + 1) none, [(((0 : W) : WithTop W), root)]⟩
    let updated := (scan weight root (graph.adjacency root) extracted).ret
    have hu : updated.queue.position[root] = none := by
      have hp := scan_presence weight root (graph.adjacency root) extracted root
      change updated.queue.position[root].isSome = q'.position[root].isSome at hp
      rw [habs] at hp
      cases hw : updated.queue.position[root] with
      | none => rfl
      | some i => simp [hw] at hp
    simp only [worker, TimeM.ret_bind, loop, liftHeap, hex]
    change (loop graph weight k updated).ret.parent[root] = none
    rw [loop_absent_parent graph weight k updated root hu]
    change (scan weight root (graph.adjacency root) extracted).ret.parent[root] = none
    rw [scan_absent_parent weight root (graph.adjacency root) extracted root habs]
    simp [extracted]

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uefc1

private lemma extraction_finite_of_crossing {W : Type uefc1} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (seen : List (Fin n)) (q q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (hex : (extractMin q).ret = some (entry, q'))
    (hc : ∀ v : Fin n, q.position[v].isSome = true ↔ v ∉ seen)
    (hb : ∀ u ∈ seen, ∀ v : Fin n, q.position[v].isSome = true →
      v ∈ graph.adjacency u → queueKey q v ≤ (weight (Sym2.mk u v) : WithTop W))
    (hcross : ∃ u ∈ seen, ∃ v : Fin n, v ∉ seen ∧ v ∈ graph.adjacency u) :
    (ofLex entry).1 ≠ ⊤ := by
  obtain ⟨u, hu, v, hv, hadj⟩ := hcross
  have hpos := (hc v).mpr hv
  have hle := extraction_cut_minimum graph weight seen q q' entry hex hb u hu v hpos hadj
  exact ne_of_lt (lt_of_le_of_lt hle (WithTop.coe_lt_top (weight (Sym2.mk u v))))

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uenk1

private lemma extracted_none_key {W : Type uenk1} [LinearOrder W] {n : Nat}
    (state : State W n) (root : Fin n) (q' : IndexedMinQueue W n)
    (entry : WithTop W ×ₗ Fin n)
    (hex : (extractMin state.queue).ret = some (entry, q'))
    (hp : ∀ v : Fin n, v ≠ root → state.queue.position[v].isSome = true →
      state.parent[v] = none → queueKey state.queue v = ⊤) :
    ∀ v : Fin n, v ≠ root → q'.position[v].isSome = true →
      state.parent[v] = none → queueKey q' v = ⊤ := by
  intro v hroot hpos hparent
  obtain ⟨hne, hold⟩ := (extraction_presence_iff state.queue q' entry hex v).mp hpos
  exact (extraction_queueKeys state.queue q' entry hex v hne).trans
    (hp v hroot hold hparent)

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uept1

private lemma extracted_parent_total {W : Type uept1} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (state : State W n) (root : Fin n) (q' : IndexedMinQueue W n)
    (entry : WithTop W ×ₗ Fin n)
    (hex : (extractMin state.queue).ret = some (entry, q'))
    (hc : ∀ v : Fin n, state.queue.position[v].isSome = true ↔
      v ∉ state.extracted.map Prod.snd)
    (hb : ∀ u ∈ state.extracted.map Prod.snd, ∀ v : Fin n,
      state.queue.position[v].isSome = true → v ∈ graph.adjacency u →
      queueKey state.queue v ≤ (weight (Sym2.mk u v) : WithTop W))
    (hnone : ∀ v : Fin n, v ≠ root → state.queue.position[v].isSome = true →
      state.parent[v] = none → queueKey state.queue v = ⊤)
    (ht : ∀ v ∈ state.extracted.map Prod.snd, v ≠ root →
      ∃ p : Fin n, state.parent[v] = some p)
    (hcross : ∃ u ∈ state.extracted.map Prod.snd, ∃ v : Fin n,
      v ∉ state.extracted.map Prod.snd ∧ v ∈ graph.adjacency u) :
    ∀ v ∈ (ofLex entry).2 :: state.extracted.map Prod.snd, v ≠ root →
      ∃ p : Fin n,
        (scan weight (ofLex entry).2 (graph.adjacency (ofLex entry).2)
          { state with queue := q', extracted := ofLex entry :: state.extracted }).ret.parent[v] =
          some p := by
  let start := { state with queue := q', extracted := ofLex entry :: state.extracted }
  intro v hv hroot
  by_cases he : v = (ofLex entry).2
  · subst v
    have hf := extraction_finite_of_crossing graph weight (state.extracted.map Prod.snd)
      state.queue q' entry hex hc hb hcross
    obtain ⟨p, hp⟩ := extraction_parent_exists state root entry q' hex hroot hf hnone
    refine ⟨p, ?_⟩
    rw [scan_absent_parent weight (ofLex entry).2 (graph.adjacency (ofLex entry).2)
      start (ofLex entry).2 (extractMin_ret state.queue q' entry hex).2.1]
    exact hp
  · have hvold := (List.mem_cons.mp hv).resolve_left he
    obtain ⟨p, hp⟩ := ht v hvold hroot
    have habs := extraction_absent state.queue q' entry hex v
      (position_none_of_seen state hc v hvold)
    refine ⟨p, ?_⟩
    rw [scan_absent_parent weight (ofLex entry).2 (graph.adjacency (ofLex entry).2) start v habs]
    exact hp

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe ulpt1

private lemma loop_parent_total {W : Type ulpt1} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n)
    (hcross : ∀ seen : List (Fin n), root ∈ seen → ∀ outside : Fin n, outside ∉ seen →
      ∃ u ∈ seen, ∃ v : Fin n, v ∉ seen ∧ v ∈ graph.adjacency u)
    (fuel : Nat) (state : State W n)
    (hr : root ∈ state.extracted.map Prod.snd)
    (hc : ∀ v : Fin n, state.queue.position[v].isSome = true ↔
      v ∉ state.extracted.map Prod.snd)
    (hb : ∀ u ∈ state.extracted.map Prod.snd, ∀ v : Fin n,
      state.queue.position[v].isSome = true → v ∈ graph.adjacency u →
      queueKey state.queue v ≤ (weight (Sym2.mk u v) : WithTop W))
    (hnone : ∀ v : Fin n, v ≠ root → state.queue.position[v].isSome = true →
      state.parent[v] = none → queueKey state.queue v = ⊤)
    (ht : ∀ v ∈ state.extracted.map Prod.snd, v ≠ root →
      ∃ p : Fin n, state.parent[v] = some p) :
    ∀ v ∈ (loop graph weight fuel state).ret.extracted.map Prod.snd, v ≠ root →
      ∃ p : Fin n, (loop graph weight fuel state).ret.parent[v] = some p := by
  induction fuel generalizing state with
  | zero => simpa [loop] using ht
  | succ fuel ih =>
    cases hex : (extractMin state.queue).ret with
    | none => simpa only [loop, TimeM.ret_bind, liftHeap, hex, TimeM.ret_pure] using ht
    | some pair =>
      rcases pair with ⟨entry, q'⟩
      let start := { state with queue := q', extracted := ofLex entry :: state.extracted }
      let updated := (scan weight (ofLex entry).2 (graph.adjacency (ofLex entry).2) start).ret
      have hx : updated.extracted = ofLex entry :: state.extracted :=
        scan_extracted weight _ _ _
      have hur : root ∈ updated.extracted.map Prod.snd := by
        rw [hx, List.map_cons]
        exact List.mem_cons_of_mem _ hr
      have huc : ∀ v : Fin n, updated.queue.position[v].isSome = true ↔
          v ∉ updated.extracted.map Prod.snd := by
        rw [hx]
        exact extracted_step_complement graph weight state q' entry hex hc
      have hue : ∀ u ∈ state.extracted.map Prod.snd, ∀ v : Fin n,
          start.queue.position[v].isSome = true → v ∈ graph.adjacency u →
          queueKey start.queue v ≤ (weight (Sym2.mk u v) : WithTop W) :=
        extraction_cut_bounds graph weight _ state.queue q' entry hex hb
      have hub : ∀ u ∈ updated.extracted.map Prod.snd, ∀ v : Fin n,
          updated.queue.position[v].isSome = true → v ∈ graph.adjacency u →
          queueKey updated.queue v ≤ (weight (Sym2.mk u v) : WithTop W) := by
        rw [hx, List.map_cons]
        exact scan_cut_bounds graph weight (ofLex entry).2 _ start hue
      have hsn : ∀ v : Fin n, v ≠ root → start.queue.position[v].isSome = true →
          start.parent[v] = none → queueKey start.queue v = ⊤ :=
        extracted_none_key state root q' entry hex hnone
      have hun := scan_none_key weight root (ofLex entry).2
        (graph.adjacency (ofLex entry).2) start hsn
      have hcur : (ofLex entry).2 ∉ state.extracted.map Prod.snd :=
        (hc _).mp (extraction_present state.queue q' entry hex)
      have hcut := hcross _ hr (ofLex entry).2 hcur
      have hut : ∀ v ∈ updated.extracted.map Prod.snd, v ≠ root →
          ∃ p : Fin n, updated.parent[v] = some p := by
        rw [hx, List.map_cons]
        exact extracted_parent_total graph weight state root q' entry hex hc hb hnone ht hcut
      simpa only [loop, TimeM.ret_bind, liftHeap, hex] using
        ih updated hur huc hub hun hut

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uppt1

private lemma prim_parent_total_of_crossing {W : Type uppt1} [LinearOrder W] [Zero W]
    {n : Nat} (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (root : Fin n)
    (hcross : ∀ seen : List (Fin n), root ∈ seen → ∀ outside : Fin n, outside ∉ seen →
      ∃ u ∈ seen, ∃ v : Fin n, v ∉ seen ∧ v ∈ graph.adjacency u) :
    ∀ v : Fin n, v ≠ root → ∃ p : Fin n, (worker graph weight root).ret.parent[v] = some p := by
  cases n with
  | zero => exact Fin.elim0 root
  | succ k =>
    let q := (initQueue (W := W) root graph.vertices (empty (k + 1))).ret
    let initial : State W (k + 1) := ⟨q, Vector.replicate (k + 1) none, []⟩
    obtain ⟨q', hex⟩ := initial_extract_root (W := W) graph root
    let entry := toLex (((0 : W) : WithTop W), root)
    let start : State W (k + 1) :=
      ⟨q', Vector.replicate (k + 1) none, [(((0 : W) : WithTop W), root)]⟩
    let updated := (scan weight root (graph.adjacency root) start).ret
    have hx : updated.extracted = [(((0 : W) : WithTop W), root)] :=
      scan_extracted weight root (graph.adjacency root) start
    have hr : root ∈ updated.extracted.map Prod.snd := by
      rw [hx]
      simp
    have hc : ∀ v : Fin (k + 1), updated.queue.position[v].isSome = true ↔
        v ∉ updated.extracted.map Prod.snd := by
      intro v
      rw [hx, scan_presence]
      change q'.position[v].isSome = true ↔ v ∉ [root]
      have hqv : q.position[v].isSome = true := initQueue_full (W := W) graph root v
      rw [extraction_presence_iff q q' entry hex v, hqv]
      simp [entry]
    have hprev : ∀ u ∈ ([] : List (Fin (k + 1))), ∀ v : Fin (k + 1),
        start.queue.position[v].isSome = true → v ∈ graph.adjacency u →
        queueKey start.queue v ≤ (weight (Sym2.mk u v) : WithTop W) := by
      intro u hu
      simp at hu
    have hb : ∀ u ∈ updated.extracted.map Prod.snd, ∀ v : Fin (k + 1),
        updated.queue.position[v].isSome = true → v ∈ graph.adjacency u →
        queueKey updated.queue v ≤ (weight (Sym2.mk u v) : WithTop W) := by
      rw [hx]
      exact scan_cut_bounds graph weight root [] start hprev
    have hninitial : ∀ v : Fin (k + 1), v ≠ root → initial.queue.position[v].isSome = true →
        initial.parent[v] = none → queueKey initial.queue v = ⊤ := by
      intro v hroot _ _
      rw [initial_queueKey, ite_eq_right hroot]
    have hns : ∀ v : Fin (k + 1), v ≠ root → start.queue.position[v].isSome = true →
        start.parent[v] = none → queueKey start.queue v = ⊤ :=
      extracted_none_key initial root q' entry hex hninitial
    have hn := scan_none_key weight root root (graph.adjacency root) start hns
    have ht : ∀ v ∈ updated.extracted.map Prod.snd, v ≠ root →
        ∃ p : Fin (k + 1), updated.parent[v] = some p := by
      rw [hx]
      intro v hv hne
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hv
      exact (hne hv).elim
    have hrun : (worker graph weight root).ret = (loop graph weight k updated).ret := by
      simp only [worker, TimeM.ret_bind, loop, liftHeap, hex]
      rfl
    have htot := loop_parent_total graph weight root hcross k updated hr hc hb hn ht
    intro v hne
    have hv := (prim_extracted_once graph weight root).2 v
    rw [hrun] at hv
    rw [hrun]
    exact htot v hv hne

end Cslib.Algorithms.Lean.Prim
