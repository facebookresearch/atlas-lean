/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all CSLibExt.Algorithms.Lean.Graph.Prim.Basic
import all CSLibExt.Algorithms.Lean.Graph.Prim.QueueInvariants
import all CSLibExt.Algorithms.Lean.Graph.Prim.ParentInvariants
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import CSLibExt.Algorithms.Lean.DataStructures.IndexedMinQueue
import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency
import Cslib.Algorithms.Lean.TimeM
import Mathlib.Data.Sym.Sym2

/-!
# Prim light cuts from the actual parent history

Adapted from CLRS, fourth edition, section 21.2, Prim's algorithm.
Proofs and executable code authored with Codex under Adam Kiezun's authorization.
-/

open Cslib.Algorithms.Lean

namespace Cslib.Algorithms.Lean.Prim

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

universe upcpt1

private lemma prim_parent_total_of_connected {W : Type upcpt1} [LinearOrder W] [Zero W]
    {n : Nat} (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (root : Fin n) (G : SimpleGraph (Fin n)) (hG : G.Connected)
    (hadj : ∀ u v : Fin n, v ∈ graph.adjacency u ↔ G.Adj u v) :
    ∀ v : Fin n, v ≠ root → ∃ p : Fin n, (worker graph weight root).ret.parent[v] = some p := by
  apply prim_parent_total_of_crossing graph weight root
  intro seen hr outside ho
  obtain ⟨walk⟩ := hG root outside
  obtain ⟨dart, _, hu, hv⟩ := walk.exists_boundary_dart {v | v ∈ seen} hr ho
  exact ⟨dart.fst, hu, dart.snd, hv, (hadj _ _).mpr dart.adj⟩

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

universe u

private lemma set_parent_edges {W : Type u} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (state : State W n) (v current : Fin n)
    (hadj : v ∈ graph.adjacency current)
    (hp : ∀ w p, state.parent[w] = some p → w ∈ graph.adjacency p) :
    ∀ w p, (state.parent.set v (some current))[w] = some p → w ∈ graph.adjacency p := by
  intro w p hw
  change (state.parent.set v.val (some current) v.isLt)[w.val] = some p at hw
  by_cases he : w = v
  · subst w
    simp only [Vector.getElem_set] at hw
    have hc : current = p := Option.some.inj hw
    simpa only [← hc] using hadj
  · have hval : v.val ≠ w.val := fun h => he (Fin.ext h.symm)
    simp only [Vector.getElem_set, ite_eq_right hval] at hw
    exact hp w p hw

private lemma scan_parent_edges {W : Type u} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (current : Fin n) (vs : List (Fin n)) (state : State W n)
    (hadj : ∀ v ∈ vs, v ∈ graph.adjacency current)
    (hp : ∀ v p, state.parent[v] = some p → v ∈ graph.adjacency p) :
    ∀ v p, (scan weight current vs state).ret.parent[v] = some p →
      v ∈ graph.adjacency p := by
  induction vs generalizing state with
  | nil => simpa [scan] using hp
  | cons v vs ih =>
    simp only [scan, TimeM.ret_bind]
    dsimp only [TimeM.bind, liftHeap]
    have hadj' : ∀ w ∈ vs, w ∈ graph.adjacency current :=
      fun w hw => hadj w (List.mem_cons_of_mem v hw)
    by_cases hlive : (Cslib.Algorithms.Lean.IndexedMinQueue.member state.queue v).ret = true
    · simp only [ite_eq_left hlive, TimeM.ret_bind]
      by_cases hlt : (weight (Sym2.mk current v) : WithTop W) < queueKey state.queue v
      · obtain ⟨q', hd⟩ := decrease_succeeds state.queue v
          (weight (Sym2.mk current v)) hlive hlt
        simp only [ite_eq_left hlt, TimeM.ret_bind, hd]
        exact ih { state with queue := q', parent := state.parent.set v (some current) }
          hadj' (set_parent_edges graph state v current (hadj v (by simp)) hp)
      · simpa only [ite_eq_right hlt] using ih state hadj' hp
    · simpa only [ite_eq_right hlive] using ih state hadj' hp

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

universe u

private lemma loop_parent_edges {W : Type u} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (fuel : Nat) (state : State W n)
    (hp : ∀ v p, state.parent[v] = some p → v ∈ graph.adjacency p) :
    ∀ v p, (loop graph weight fuel state).ret.parent[v] = some p →
      v ∈ graph.adjacency p := by
  induction fuel generalizing state with
  | zero => simpa [loop] using hp
  | succ fuel ih =>
    cases hex : (Cslib.Algorithms.Lean.IndexedMinQueue.extractMin state.queue).ret with
    | none => simpa only [loop, TimeM.ret_bind, liftHeap, hex, TimeM.ret_pure] using hp
    | some pair =>
      rcases pair with ⟨entry, q'⟩
      simp only [loop, TimeM.ret_bind, liftHeap, hex]
      apply ih
      exact scan_parent_edges graph weight (ofLex entry).2
        (graph.adjacency (ofLex entry).2)
        { state with queue := q', extracted := ofLex entry :: state.extracted }
        (fun v hv => hv) hp

private lemma prim_parent_edges {W : Type u} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    ∀ v p, (worker graph weight root).ret.parent[v] = some p → v ∈ graph.adjacency p := by
  simp only [worker, TimeM.ret_bind]
  apply loop_parent_edges
  intro v p hp
  simp at hp

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uprz1

private lemma set_parent_realizes {W : Type uprz1} [LinearOrder W] {n : Nat}
    (weight : Sym2 (Fin n) → W) (state : State W n) (q' : IndexedMinQueue W n)
    (v current : Fin n)
    (hd : (decreaseKey state.queue v (weight (Sym2.mk current v))).ret = some q')
    (hp : ∀ w p, state.queue.position[w].isSome = true → state.parent[w] = some p →
      queueKey state.queue w = (weight (Sym2.mk p w) : WithTop W)) :
    ∀ w p, q'.position[w].isSome = true → (state.parent.set v (some current))[w] = some p →
      queueKey q' w = (weight (Sym2.mk p w) : WithTop W) := by
  intro w p hw hparent
  have hk := decrease_queueKeys state.queue q' v (weight (Sym2.mk current v)) hd
  change (state.parent.set v.val (some current) v.isLt)[w.val] = some p at hparent
  by_cases he : w = v
  · subst w
    simp only [Vector.getElem_set] at hparent
    have hc : current = p := Option.some.inj hparent
    simpa only [← hc] using hk.1
  · have hval : v.val ≠ w.val := fun h => he (Fin.ext h.symm)
    simp only [Vector.getElem_set, ite_eq_right hval] at hparent
    have hwold :=
      ((decreaseKey_ret state.queue q' v (weight (Sym2.mk current v)) hd).2 w).symm.trans hw
    exact (hk.2 w he).trans (hp w p hwold hparent)

private lemma scan_parent_realizes {W : Type uprz1} [LinearOrder W] {n : Nat}
    (weight : Sym2 (Fin n) → W) (current : Fin n) (vs : List (Fin n)) (state : State W n)
    (hp : ∀ w p, state.queue.position[w].isSome = true → state.parent[w] = some p →
      queueKey state.queue w = (weight (Sym2.mk p w) : WithTop W)) :
    ∀ w p, (scan weight current vs state).ret.queue.position[w].isSome = true →
      (scan weight current vs state).ret.parent[w] = some p →
      queueKey (scan weight current vs state).ret.queue w = (weight (Sym2.mk p w) : WithTop W) := by
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
          (set_parent_realizes weight state q' v current hd hp)
      · simpa only [ite_eq_right hlt] using ih state hp
    · simpa only [ite_eq_right hlive] using ih state hp

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

universe upgs1

private lemma prim_parent_graph_le {W : Type upgs1} [LinearOrder W] [Zero W]
    {n : Nat} (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (root : Fin n) (G : SimpleGraph (Fin n))
    (hadj : ∀ u v : Fin n, v ∈ graph.adjacency u ↔ G.Adj u v) :
    SimpleGraph.fromRel
      (fun u v : Fin n => (worker graph weight root).ret.parent[v] = some u) ≤ G := by
  intro u v h
  rw [SimpleGraph.fromRel_adj] at h
  rcases h.2 with h | h
  · exact (hadj u v).mp (prim_parent_edges graph weight root v u h)
  · exact ((hadj v u).mp (prim_parent_edges graph weight root u v h)).symm

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uepcm1

private lemma extraction_parent_cut_minimum {W : Type uepcm1} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (state : State W n) (q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (hex : (extractMin state.queue).ret = some (entry, q'))
    (hc : ∀ v : Fin n, state.queue.position[v].isSome = true ↔
      v ∉ state.extracted.map Prod.snd)
    (hb : ∀ u ∈ state.extracted.map Prod.snd, ∀ v : Fin n,
      state.queue.position[v].isSome = true → v ∈ graph.adjacency u →
      queueKey state.queue v ≤ (weight (Sym2.mk u v) : WithTop W))
    (hr : ∀ v p : Fin n, state.queue.position[v].isSome = true →
      state.parent[v] = some p → queueKey state.queue v = (weight (Sym2.mk p v) : WithTop W))
    (p : Fin n) (hp : state.parent[(ofLex entry).2] = some p) :
    ∀ u ∈ state.extracted.map Prod.snd, ∀ v : Fin n,
      v ∉ state.extracted.map Prod.snd → v ∈ graph.adjacency u →
      weight (Sym2.mk p (ofLex entry).2) ≤ weight (Sym2.mk u v) := by
  have hpos := extraction_present state.queue q' entry hex
  have hkey := heap_entry_key state.queue entry
    (MinHeap.extractMin_mem (extractMin_ret state.queue q' entry hex).1)
  have hreal := hr (ofLex entry).2 p hpos hp
  intro u hu v hv hadj
  have hle := extraction_cut_minimum graph weight (state.extracted.map Prod.snd)
    state.queue q' entry hex hb u hu v ((hc v).mpr hv) hadj
  rw [← hkey, hreal] at hle
  exact WithTop.coe_le_coe.mp hle

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe upsc1

@[no_expose] private def parentSafeCuts {W : Type upsc1} [LE W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (parents : Vector (Option (Fin n)) n) (seen : List (Fin n)) : Prop :=
  ∀ v p : Fin n, v ∈ seen → parents[v] = some p →
    ∃ before after : List (Fin n), seen = before ++ v :: after ∧ p ∈ after ∧
      ∀ u ∈ after, ∀ w : Fin n, w ∉ after → w ∈ graph.adjacency u →
        weight (Sym2.mk p v) ≤ weight (Sym2.mk u w)

private lemma extracted_parent_safeCuts {W : Type upsc1} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (state : State W n) (q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (hex : (extractMin state.queue).ret = some (entry, q'))
    (hc : ∀ w : Fin n, state.queue.position[w].isSome = true ↔
      w ∉ state.extracted.map Prod.snd)
    (hp : ∀ w p : Fin n, state.parent[w] = some p → p ∈ state.extracted.map Prod.snd)
    (hb : ∀ u ∈ state.extracted.map Prod.snd, ∀ v : Fin n,
      state.queue.position[v].isSome = true → v ∈ graph.adjacency u →
      queueKey state.queue v ≤ (weight (Sym2.mk u v) : WithTop W))
    (hr : ∀ v p : Fin n, state.queue.position[v].isSome = true →
      state.parent[v] = some p → queueKey state.queue v = (weight (Sym2.mk p v) : WithTop W))
    (hh : parentSafeCuts graph weight state.parent (state.extracted.map Prod.snd)) :
    parentSafeCuts graph weight
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
    exact ⟨[], state.extracted.map Prod.snd, rfl, hp _ _ hparent,
      extraction_parent_cut_minimum graph weight state q' entry hex hc hb hr p hparent⟩
  · have hvold : v ∈ state.extracted.map Prod.snd :=
      (List.mem_cons.mp hv).resolve_left he
    have habs := extraction_absent state.queue q' entry hex v
      (position_none_of_seen state hc v hvold)
    have hf := scan_absent_parent weight (ofLex entry).2 (graph.adjacency (ofLex entry).2)
      start v habs
    rw [hf] at hparent
    obtain ⟨before, after, hsplit, hpmem, hmin⟩ := hh v p hvold hparent
    exact ⟨(ofLex entry).2 :: before, after, by simp only [List.cons_append, hsplit],
      hpmem, hmin⟩

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uepr1

private lemma extraction_parent_realizes {W : Type uepr1} [LinearOrder W] {n : Nat}
    (state : State W n) (q' : IndexedMinQueue W n) (entry : WithTop W ×ₗ Fin n)
    (hex : (extractMin state.queue).ret = some (entry, q'))
    (weight : Sym2 (Fin n) → W)
    (hr : ∀ v p : Fin n, state.queue.position[v].isSome = true →
      state.parent[v] = some p → queueKey state.queue v = (weight (Sym2.mk p v) : WithTop W)) :
    ∀ v p : Fin n, q'.position[v].isSome = true → state.parent[v] = some p →
      queueKey q' v = (weight (Sym2.mk p v) : WithTop W) := by
  intro v p hv hp
  have hs := extractMin_ret state.queue q' entry hex
  have hne : v ≠ (ofLex entry).2 := by
    intro he
    subst v
    simp [hs.2.1] at hv
  have hpos : state.queue.position[v].isSome = true := (hs.2.2 v hne).symm.trans hv
  rw [extraction_queueKeys state.queue q' entry hex v hne]
  exact hr v p hpos hp

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe ulpsc1

private lemma loop_parent_safeCuts {W : Type ulpsc1} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (fuel : Nat) (state : State W n)
    (hc : ∀ w : Fin n, state.queue.position[w].isSome = true ↔
      w ∉ state.extracted.map Prod.snd)
    (hp : ∀ w p : Fin n, state.parent[w] = some p → p ∈ state.extracted.map Prod.snd)
    (hb : ∀ u ∈ state.extracted.map Prod.snd, ∀ v : Fin n,
      state.queue.position[v].isSome = true → v ∈ graph.adjacency u →
      queueKey state.queue v ≤ (weight (Sym2.mk u v) : WithTop W))
    (hr : ∀ v p : Fin n, state.queue.position[v].isSome = true →
      state.parent[v] = some p → queueKey state.queue v = (weight (Sym2.mk p v) : WithTop W))
    (hh : parentSafeCuts graph weight state.parent (state.extracted.map Prod.snd)) :
    parentSafeCuts graph weight (loop graph weight fuel state).ret.parent
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
      have huc : ∀ w : Fin n, updated.queue.position[w].isSome = true ↔
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
      have he := extraction_cut_bounds graph weight (state.extracted.map Prod.snd)
        state.queue q' entry hex hb
      have hub : ∀ u ∈ updated.extracted.map Prod.snd, ∀ v : Fin n,
          updated.queue.position[v].isSome = true → v ∈ graph.adjacency u →
          queueKey updated.queue v ≤ (weight (Sym2.mk u v) : WithTop W) := by
        rw [hx, List.map_cons]
        exact scan_cut_bounds graph weight (ofLex entry).2 (state.extracted.map Prod.snd) start he
      have her := extraction_parent_realizes state q' entry hex weight hr
      have hur : ∀ v p : Fin n, updated.queue.position[v].isSome = true →
          updated.parent[v] = some p →
          queueKey updated.queue v = (weight (Sym2.mk p v) : WithTop W) :=
        scan_parent_realizes weight (ofLex entry).2 (graph.adjacency (ofLex entry).2) start her
      have huh : parentSafeCuts graph weight updated.parent
          (updated.extracted.map Prod.snd) := by
        rw [hx, List.map_cons]
        exact extracted_parent_safeCuts graph weight state q' entry hex hc hp hb hr hh
      simpa only [loop, TimeM.ret_bind, liftHeap, hex] using ih updated huc hup hub hur huh

private lemma prim_parent_safeCuts {W : Type ulpsc1} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    parentSafeCuts graph weight (worker graph weight root).ret.parent
      ((worker graph weight root).ret.extracted.map Prod.snd) := by
  simp only [worker, TimeM.ret_bind]
  apply loop_parent_safeCuts
  · intro w
    simpa using initQueue_full (W := W) graph root w
  · intro w p hp
    simp at hp
  · intro u hu
    simp at hu
  · intro v p _ hp
    simp at hp
  · intro v p hv
    simp at hv

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

universe upplc1

private lemma prim_parent_light_cut {W : Type upplc1} [LinearOrder W] [Zero W]
    {n : Nat} (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (root : Fin n) (G : SimpleGraph (Fin n)) (hG : G.Connected)
    (hadj : ∀ u v : Fin n, v ∈ graph.adjacency u ↔ G.Adj u v)
    (v : Fin n) (hne : v ≠ root) :
    ∃ p : Fin n, ∃ before after : List (Fin n),
      (worker graph weight root).ret.parent[v] = some p ∧
      (worker graph weight root).ret.extracted.map Prod.snd = before ++ v :: after ∧
      p ∈ after ∧ v ∉ after ∧ G.Adj p v ∧
      ∀ u ∈ after, ∀ w : Fin n, w ∉ after → G.Adj u w →
        weight (Sym2.mk p v) ≤ weight (Sym2.mk u w) := by
  obtain ⟨p, hp⟩ := prim_parent_total_of_connected graph weight root G hG hadj v hne
  have hrun := prim_extracted_once graph weight root
  obtain ⟨before, after, hsplit, hpmem, hmin⟩ :=
    prim_parent_safeCuts graph weight root v p (hrun.2 v) hp
  have hparts := List.nodup_append.mp (hsplit ▸ hrun.1)
  refine ⟨p, before, after, hp, hsplit, hpmem,
    (List.nodup_cons.mp hparts.2.1).1, ?_, ?_⟩
  · exact (hadj p v).mp (prim_parent_edges graph weight root v p hp)
  · intro u hu w hw hadjG
    exact hmin u hu w hw ((hadj u w).mpr hadjG)

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

private lemma parent_history_suffix_closed {n : Nat}
    (parents : Vector (Option (Fin n)) n) (seen : List (Fin n))
    (hn : seen.Nodup) (hh : parentHistory parents seen)
    (before after : List (Fin n)) (hsplit : seen = before ++ after) :
    ∀ v ∈ after, ∀ p : Fin n, parents[v] = some p → p ∈ after := by
  intro v hv p hp
  have hvseen : v ∈ seen := by
    rw [hsplit]
    exact List.mem_append_right before hv
  obtain ⟨before', after', hsplit', hpmem⟩ := hh v p hvseen hp
  have hpseen : p ∈ seen := by
    rw [hsplit']
    exact List.mem_append_right before' (List.mem_cons_of_mem v hpmem)
  by_contra hpnot
  have hpbefore : p ∈ before := by
    rw [hsplit] at hpseen
    exact (List.mem_append.mp hpseen).resolve_right hpnot
  have hparts := List.nodup_append.mp (hsplit ▸ hn)
  have hvnot : v ∉ before := by
    intro hmem
    exact (hparts.2.2 v hmem v hv) rfl
  have hvi : before.length ≤ seen.idxOf v := by
    rw [hsplit, List.idxOf_append_of_notMem hvnot]
    omega
  have hpi : seen.idxOf p < before.length := by
    rw [hsplit, List.idxOf_append_of_mem hpbefore]
    exact List.idxOf_lt_length_of_mem hpbefore
  have horder := history_rank parents seen hn hh v p hvseen hp
  omega

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

@[no_expose] private def parentGraphOn {n : Nat}
    (parents : Vector (Option (Fin n)) n) (ids : List (Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v : Fin n => v ∈ ids ∧ parents[v] = some u)

private lemma parent_graph_on_respects_suffix {n : Nat}
    (parents : Vector (Option (Fin n)) n) (seen : List (Fin n))
    (hn : seen.Nodup) (hh : parentHistory parents seen)
    (before after : List (Fin n)) (hsplit : seen = before ++ after) :
    ∀ u v : Fin n, (parentGraphOn parents after).Adj u v → (u ∈ after ↔ v ∈ after) := by
  intro u v h
  change (SimpleGraph.fromRel (fun a b : Fin n => b ∈ after ∧ parents[b] = some a)).Adj u v at h
  rw [SimpleGraph.fromRel_adj] at h
  rcases h.2 with h | h
  · exact iff_of_true (parent_history_suffix_closed parents seen hn hh before after hsplit
      v h.1 u h.2) h.1
  · exact iff_of_true h.1 (parent_history_suffix_closed parents seen hn hh before after hsplit
      u h.1 v h.2)

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

universe upct1

private lemma parent_safeCuts_tail {W : Type upct1} [LE W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (parents : Vector (Option (Fin n)) n) (v : Fin n) (tail : List (Fin n))
    (hn : (v :: tail).Nodup) (hs : parentSafeCuts graph weight parents (v :: tail)) :
    parentSafeCuts graph weight parents tail := by
  intro w p hw hp
  obtain ⟨before, after, hsplit, hpmem, hmin⟩ :=
    hs w p (List.mem_cons_of_mem v hw) hp
  have hne : w ≠ v := by
    intro h
    subst w
    exact (List.nodup_cons.mp hn).1 hw
  cases before with
  | nil =>
    have he : v = w := (List.cons.inj hsplit).1
    exact False.elim (hne he.symm)
  | cons a before =>
    have he : tail = before ++ w :: after := (List.cons.inj hsplit).2
    exact ⟨before, after, he, hpmem, hmin⟩

private lemma parent_safeCuts_head {W : Type upct1} [LE W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (parents : Vector (Option (Fin n)) n) (v p : Fin n) (tail : List (Fin n))
    (hn : (v :: tail).Nodup) (hs : parentSafeCuts graph weight parents (v :: tail))
    (hp : parents[v] = some p) :
    p ∈ tail ∧ ∀ u ∈ tail, ∀ w : Fin n, w ∉ tail → w ∈ graph.adjacency u →
      weight (Sym2.mk p v) ≤ weight (Sym2.mk u w) := by
  obtain ⟨before, after, hsplit, hpmem, hmin⟩ := hs v p (by simp) hp
  cases before with
  | nil =>
    have he : tail = after := (List.cons.inj hsplit).2
    subst after
    exact ⟨hpmem, hmin⟩
  | cons a before =>
    have he : v = a := (List.cons.inj hsplit).1
    have hparts := List.nodup_append.mp (hsplit ▸ hn)
    have hvbefore : v ∈ a :: before := by simp [he]
    exact False.elim ((hparts.2.2 v hvbefore v (by simp)) rfl)

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

private lemma parent_graph_on_cons_some {n : Nat}
    (parents : Vector (Option (Fin n)) n) (v p : Fin n) (tail : List (Fin n))
    (hp : parents[v] = some p) :
    parentGraphOn parents (v :: tail) = parentGraphOn parents tail ⊔ SimpleGraph.edge p v := by
  ext u w
  simp only [parentGraphOn, SimpleGraph.fromRel_adj, SimpleGraph.sup_adj,
    SimpleGraph.edge_adj, List.mem_cons]
  constructor
  · rintro ⟨hne, h | h⟩
    · rcases h with ⟨hw, hr⟩
      rcases hw with hw | hw
      · subst w
        have he : p = u := Option.some.inj (hp.symm.trans hr)
        exact Or.inr ⟨Or.inl ⟨he.symm, rfl⟩, hne⟩
      · exact Or.inl ⟨hne, Or.inl ⟨hw, hr⟩⟩
    · rcases h with ⟨hu, hr⟩
      rcases hu with hu | hu
      · subst u
        have he : p = w := Option.some.inj (hp.symm.trans hr)
        exact Or.inr ⟨Or.inr ⟨rfl, he.symm⟩, hne⟩
      · exact Or.inl ⟨hne, Or.inr ⟨hu, hr⟩⟩
  · intro h
    rcases h with h | h
    · rcases h with ⟨hne, h | h⟩
      · exact ⟨hne, Or.inl ⟨Or.inr h.1, h.2⟩⟩
      · exact ⟨hne, Or.inr ⟨Or.inr h.1, h.2⟩⟩
    · rcases h with ⟨h | h, hne⟩
      · exact ⟨hne, Or.inl ⟨Or.inl h.2, by simpa only [h.1, h.2] using hp⟩⟩
      · exact ⟨hne, Or.inr ⟨Or.inl h.1, by simpa only [h.1, h.2] using hp⟩⟩

private lemma parent_graph_on_cons_none {n : Nat}
    (parents : Vector (Option (Fin n)) n) (v : Fin n) (tail : List (Fin n))
    (hp : parents[v] = none) :
    parentGraphOn parents (v :: tail) = parentGraphOn parents tail := by
  ext u w
  simp only [parentGraphOn, SimpleGraph.fromRel_adj, List.mem_cons]
  constructor
  · rintro ⟨hne, h | h⟩
    · rcases h with ⟨hw, hr⟩
      rcases hw with hw | hw
      · subst w
        simp only [hp] at hr
        cases hr
      · exact ⟨hne, Or.inl ⟨hw, hr⟩⟩
    · rcases h with ⟨hu, hr⟩
      rcases hu with hu | hu
      · subst u
        simp only [hp] at hr
        cases hr
      · exact ⟨hne, Or.inr ⟨hu, hr⟩⟩
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, Or.inl ⟨Or.inr h.1, h.2⟩⟩
    · exact ⟨hne, Or.inr ⟨Or.inr h.1, h.2⟩⟩

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

end Cslib.Algorithms.Lean.Prim
