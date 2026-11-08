/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.Prim.Basic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Nat.Log

import all CSLibExt.Algorithms.Lean.Graph.Prim.Basic
import all CSLibExt.Algorithms.Lean.Graph.Prim.QueueInvariants
import CSLibExt.Algorithms.Lean.DataStructures.IndexedMinQueue
import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency
import Cslib.Algorithms.Lean.TimeM
import Mathlib.Data.Sym.Sym2

/-!
# Same-execution Prim heap and graph event bounds

Adapted from CLRS, fourth edition, section 21.2, Prim's algorithm.
Proofs and executable code authored with Codex under Adam Kiezun's authorization.
-/

open Cslib.Algorithms.Lean

namespace Cslib.Algorithms.Lean.Prim

universe usi2

private lemma scan_inspections {W : Type usi2} [LinearOrder W] {n : Nat}
    (weight : Sym2 (Fin n) → W) (current : Fin n) (vs : List (Fin n))
    (state : State W n) : (scan weight current vs state).time.2.1 = vs.length := by
  induction vs generalizing state with
  | nil => simp [scan]
  | cons v vs ih =>
    by_cases hlive : (Cslib.Algorithms.Lean.IndexedMinQueue.member state.queue v).ret = true
    · by_cases hlt : (weight (Sym2.mk current v) : WithTop W) < queueKey state.queue v
      · obtain ⟨q', hd⟩ := decrease_succeeds state.queue v
          (weight (Sym2.mk current v)) hlive hlt
        simp [scan, TimeM.bind, liftHeap, hlive, hlt, hd, ih, Nat.add_comm]
      · simp [scan, TimeM.bind, liftHeap, hlive, hlt, ih, Nat.add_comm]
    · simp [scan, TimeM.bind, liftHeap, hlive, ih, Nat.add_comm]

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe ulis1

private lemma loop_inspection_sum {W : Type ulis1} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (fuel : Nat) (state : State W n) :
    (loop graph weight fuel state).time.2.1 +
        (state.extracted.map (fun entry => (graph.adjacency entry.2).length)).sum =
      ((loop graph weight fuel state).ret.extracted.map
        (fun entry => (graph.adjacency entry.2).length)).sum := by
  induction fuel generalizing state with
  | zero => simp [loop]
  | succ fuel ih =>
    cases hex : (extractMin state.queue).ret with
    | none => simp [loop, liftHeap, hex]
    | some pair =>
      rcases pair with ⟨entry, q'⟩
      let updated := (scan weight (ofLex entry).2 (graph.adjacency (ofLex entry).2)
        { state with queue := q', extracted := ofLex entry :: state.extracted }).ret
      have hx : updated.extracted = ofLex entry :: state.extracted :=
        scan_extracted weight _ _ _
      have h := ih updated
      rw [hx, List.map_cons, List.sum_cons] at h
      simp only [loop, TimeM.time_bind, liftHeap, hex]
      simp only [Prod.snd_add, Prod.fst_add, Nat.zero_add]
      rw [scan_inspections]
      change (graph.adjacency (ofLex entry).2).length +
        (loop graph weight fuel updated).time.2.1 +
          (state.extracted.map (fun entry => (graph.adjacency entry.2).length)).sum =
          ((loop graph weight fuel updated).ret.extracted.map
            (fun entry => (graph.adjacency entry.2).length)).sum
      omega

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uist2

private lemma initQueue_scalar_times {W : Type uist2} [LinearOrder W] [Zero W] {n : Nat}
    (root : Fin n) (vs : List (Fin n)) (q : IndexedMinQueue W n) :
    (initQueue root vs q).time.2 = (0, 0) := by
  induction vs generalizing q with
  | nil => rfl
  | cons v vs ih =>
    simp only [initQueue, TimeM.time_bind]
    dsimp only [liftHeap]
    cases hins : (insert q v (if v = root then ((0 : W) : WithTop W) else ⊤)).ret with
    | none => simp only [TimeM.time_pure]; rfl
    | some q' => simp only [Prod.snd_add, ih]; rfl

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe ulsb1

private lemma loop_tests_le_inspections {W : Type ulsb1} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (fuel : Nat) (state : State W n) :
    (loop graph weight fuel state).time.2.2 ≤ (loop graph weight fuel state).time.2.1 := by
  induction fuel generalizing state with
  | zero => simp [loop]
  | succ fuel ih =>
    cases hex : (extractMin state.queue).ret with
    | none => simp [loop, liftHeap, hex]
    | some pair =>
      rcases pair with ⟨entry, q'⟩
      let start := { state with queue := q', extracted := ofLex entry :: state.extracted }
      let updated := (scan weight (ofLex entry).2 (graph.adjacency (ofLex entry).2) start).ret
      have hs := scan_tests_le weight (ofLex entry).2 (graph.adjacency (ofLex entry).2) start
      rw [← scan_inspections weight (ofLex entry).2 (graph.adjacency (ofLex entry).2) start] at hs
      simpa [loop, TimeM.bind, liftHeap, hex, start, updated] using Nat.add_le_add hs (ih updated)

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe upsc1

private lemma prim_inspection_trace {W : Type upsc1} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    (worker graph weight root).time.2.1 =
      ((worker graph weight root).ret.extracted.map
        (fun entry => (graph.adjacency entry.2).length)).sum := by
  let q := (initQueue (W := W) root graph.vertices (empty n)).ret
  let state : State W n := ⟨q, Vector.replicate n none, []⟩
  have hi := loop_inspection_sum graph weight n state
  simp only [state, List.map_nil, List.sum_nil, Nat.add_zero] at hi
  simp only [worker, TimeM.time_bind, Prod.snd_add, Prod.fst_add,
    initQueue_scalar_times, Nat.zero_add]
  exact hi

private lemma prim_extracted_perm {W : Type upsc1} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    ((worker graph weight root).ret.extracted.map Prod.snd).Perm graph.vertices := by
  have hp := prim_extracted_once graph weight root
  apply (List.perm_ext_iff_of_nodup hp.1 graph.vertices_nodup).mpr
  intro w
  exact iff_of_true (hp.2 w) (graph.vertices_complete w)

private lemma worker_inspections {W : Type upsc1} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    (worker graph weight root).time.2.1 =
      (graph.vertices.map (fun v => (graph.adjacency v).length)).sum := by
  rw [prim_inspection_trace]
  have hs := ((prim_extracted_perm graph weight root).map
    (fun v => (graph.adjacency v).length)).sum_eq
  simpa only [List.map_map, Function.comp_def] using hs

private lemma prim_tests_le_inspections {W : Type upsc1} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    (worker graph weight root).time.2.2 ≤ (worker graph weight root).time.2.1 := by
  simp only [worker, TimeM.time_bind, Prod.snd_add, Prod.fst_add,
    initQueue_scalar_times, Nat.zero_add]
  exact loop_tests_le_inspections graph weight n _

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uhcc1

private lemma capacity_log {W : Type uhcc1} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) : Nat.log2 (q.heap.data.size + 1) ≤ Nat.log2 (n + 1) := by
  simpa only [Nat.log2_eq_log_two] using
    Nat.log_monotone (Nat.add_le_add_right q.capacity 1)

private lemma insert_capacity_time {W : Type uhcc1} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) (key : WithTop W) (c : Fin 5) :
    (insert q v key).time c ≤ 20 * (Nat.log2 (n + 1) + 1) := by
  have ht := insert_time q v key c
  have hl := capacity_log q
  omega

private lemma decrease_capacity_time {W : Type uhcc1} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) (key : W) (c : Fin 5) :
    (decreaseKey q v key).time c ≤ 20 * (Nat.log2 (n + 1) + 1) := by
  have ht := decreaseKey_time q v key c
  have hl := capacity_log q
  omega

private lemma extraction_capacity_time {W : Type uhcc1} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (c : Fin 5) :
    (extractMin q).time c ≤ 20 * (Nat.log2 (n + 1) + 1) := by
  have ht := extractMin_time q c
  have hl := capacity_log q
  omega

private lemma membership_time_le_one {W : Type uhcc1} [LinearOrder W] {n : Nat}
    (q : IndexedMinQueue W n) (v : Fin n) (c : Fin 5) :
    (Cslib.Algorithms.Lean.IndexedMinQueue.member q v).time c ≤ 1 := by
  by_cases hc : c = 2 <;> simp [member_time, hc]

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uihc1

private lemma initQueue_heap_cost {W : Type uihc1} [LinearOrder W] [Zero W] {n : Nat}
    (root : Fin n) (vs : List (Fin n)) (q : IndexedMinQueue W n) (c : Fin 5) :
    (initQueue root vs q).time.1 c ≤ vs.length * (20 * (Nat.log2 (n + 1) + 1)) := by
  induction vs generalizing q with
  | nil => simp [initQueue]
  | cons v vs ih =>
    have ht := insert_capacity_time q v (if v = root then ((0 : W) : WithTop W) else ⊤) c
    simp only [initQueue, TimeM.time_bind]
    dsimp only [liftHeap]
    cases hins : (insert q v (if v = root then ((0 : W) : WithTop W) else ⊤)).ret with
    | none =>
      change (insert q v (if v = root then ((0 : W) : WithTop W) else ⊤)).time c + 0 ≤ _
      rw [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    | some q' =>
      change (insert q v (if v = root then ((0 : W) : WithTop W) else ⊤)).time c +
        (initQueue root vs q').time.1 c ≤ _
      have hi := ih q'
      rw [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe ushc1

private lemma scan_heap_cost {W : Type ushc1} [LinearOrder W] {n : Nat}
    (weight : Sym2 (Fin n) → W) (current : Fin n) (vs : List (Fin n))
    (state : State W n) (c : Fin 5) :
    (scan weight current vs state).time.1 c ≤
      vs.length * (20 * (Nat.log2 (n + 1) + 1) + 1) := by
  induction vs generalizing state with
  | nil => simp [scan]
  | cons v vs ih =>
    have hm := membership_time_le_one state.queue v c
    by_cases hlive : (Cslib.Algorithms.Lean.IndexedMinQueue.member state.queue v).ret = true
    · by_cases hlt : (weight (Sym2.mk current v) : WithTop W) < queueKey state.queue v
      · obtain ⟨q', hd⟩ := decrease_succeeds state.queue v
          (weight (Sym2.mk current v)) hlive hlt
        let updated := { state with queue := q', parent := state.parent.set v (some current) }
        have ht := decrease_capacity_time state.queue v (weight (Sym2.mk current v)) c
        have hi := ih updated
        simp [scan, TimeM.bind, liftHeap, hlive, hlt, hd]
        change (Cslib.Algorithms.Lean.IndexedMinQueue.member state.queue v).time c +
          ((decreaseKey state.queue v (weight (Sym2.mk current v))).time c +
            (scan weight current vs updated).time.1 c) ≤ _
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · have hi := ih state
        simp [scan, TimeM.bind, liftHeap, hlive, hlt]
        rw [Nat.add_mul, Nat.one_mul]
        omega
    · have hi := ih state
      simp [scan, TimeM.bind, liftHeap, hlive]
      rw [Nat.add_mul, Nat.one_mul]
      omega

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe ulhc1

private lemma loop_heap_cost {W : Type ulhc1} [LinearOrder W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W)
    (fuel : Nat) (state : State W n) (c : Fin 5) :
    (loop graph weight fuel state).time.1 c ≤
      fuel * (20 * (Nat.log2 (n + 1) + 1)) +
        (20 * (Nat.log2 (n + 1) + 1) + 1) * (loop graph weight fuel state).time.2.1 := by
  induction fuel generalizing state with
  | zero => simp [loop]
  | succ fuel ih =>
    let B := 20 * (Nat.log2 (n + 1) + 1)
    have ht := extraction_capacity_time state.queue c
    cases hex : (extractMin state.queue).ret with
    | none =>
      simp [loop, liftHeap, hex]
      rw [Nat.add_mul, Nat.one_mul]
      omega
    | some pair =>
      rcases pair with ⟨entry, q'⟩
      let start := { state with queue := q', extracted := ofLex entry :: state.extracted }
      let updated := (scan weight (ofLex entry).2 (graph.adjacency (ofLex entry).2) start).ret
      have hs := scan_heap_cost weight (ofLex entry).2 (graph.adjacency (ofLex entry).2) start c
      have hi := ih updated
      simp only [loop, TimeM.time_bind, liftHeap, hex,
        Prod.fst_add, Prod.snd_add, Nat.zero_add]
      rw [scan_inspections]
      change (extractMin state.queue).time c +
        ((scan weight (ofLex entry).2 (graph.adjacency (ofLex entry).2) start).time.1 c +
          (loop graph weight fuel updated).time.1 c) ≤
            (fuel + 1) * B + (B + 1) *
              ((graph.adjacency (ofLex entry).2).length + (loop graph weight fuel updated).time.2.1)
      change (extractMin state.queue).time c ≤ B at ht
      change (scan weight (ofLex entry).2 (graph.adjacency (ofLex entry).2) start).time.1 c ≤
        (graph.adjacency (ofLex entry).2).length * (B + 1) at hs
      change (loop graph weight fuel updated).time.1 c ≤
        fuel * B + (B + 1) * (loop graph weight fuel updated).time.2.1 at hi
      rw [Nat.add_mul fuel 1 B, Nat.one_mul,
        Nat.mul_add (B + 1) (graph.adjacency (ofLex entry).2).length
          (loop graph weight fuel updated).time.2.1,
        ← Nat.mul_comm (graph.adjacency (ofLex entry).2).length (B + 1)]
      omega

end Cslib.Algorithms.Lean.Prim

private lemma event_bound_arithmetic (n b s : Nat) :
    n * b + n * b + (b + 1) * s = b * (2 * n + s) + s := by
  have htwo : b * (2 * n) = n * b + n * b := by
    rw [Nat.two_mul, Nat.mul_add]
    simp only [Nat.mul_comm b n]
  rw [Nat.mul_add b (2 * n) s, Nat.add_mul b 1 s, Nat.one_mul, htwo]
  omega

namespace Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean.IndexedMinQueue

universe uphc1

private lemma prim_heap_cost {W : Type uphc1} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) (c : Fin 5) :
    (worker graph weight root).time.1 c ≤
      20 * (2 * n + (worker graph weight root).time.2.1) * (Nat.log2 (n + 1) + 1) +
        (worker graph weight root).time.2.1 := by
  let B := 20 * (Nat.log2 (n + 1) + 1)
  let q := (initQueue (W := W) root graph.vertices (empty n)).ret
  let state : State W n := ⟨q, Vector.replicate n none, []⟩
  have hs := initQueue_heap_cost root graph.vertices (empty (W := W) n) c
  rw [vertices_length graph] at hs
  have hl := loop_heap_cost graph weight n state c
  have ht := Nat.add_le_add hs hl
  have hbound : (worker graph weight root).time.1 c ≤
      n * B + n * B + (B + 1) * (worker graph weight root).time.2.1 := by
    simp only [worker, TimeM.time_bind, Prod.fst_add, Prod.snd_add,
      initQueue_scalar_times, Nat.zero_add]
    change (initQueue (W := W) root graph.vertices (empty n)).time.1 c +
      (loop graph weight n state).time.1 c ≤
        n * B + n * B + (B + 1) * (loop graph weight n state).time.2.1
    change (initQueue (W := W) root graph.vertices (empty n)).time.1 c +
      (loop graph weight n state).time.1 c ≤
        n * B + (n * B + (B + 1) * (loop graph weight n state).time.2.1) at ht
    omega
  rw [event_bound_arithmetic] at hbound
  dsimp only [B] at hbound
  rw [Nat.mul_right_comm 20 (Nat.log2 (n + 1) + 1)
    (2 * n + (worker graph weight root).time.2.1)] at hbound
  exact hbound

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

end Cslib.Algorithms.Lean.Prim

open Cslib.Algorithms.Lean
open scoped BigOperators

namespace Cslib.Algorithms.Lean.Prim

private lemma adjacency_length_degree {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (G : SimpleGraph (Fin n))
    (hadj : ∀ u v : Fin n, v ∈ graph.adjacency u ↔ G.Adj u v)
    (hn : ∀ u : Fin n, (graph.adjacency u).Nodup) (u : Fin n) :
    by
      classical
      exact (graph.adjacency u).length = G.degree u := by
  classical
  have heq : (graph.adjacency u).toFinset = G.neighborFinset u := by
    ext v
    simp [hadj]
  calc
    (graph.adjacency u).length = (graph.adjacency u).toFinset.card :=
      (List.toFinset_card_of_nodup (hn u)).symm
    _ = (G.neighborFinset u).card := congrArg Finset.card heq
    _ = G.degree u := G.card_neighborFinset_eq_degree u

private lemma adjacency_sum_twice_edges {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (G : SimpleGraph (Fin n))
    (hadj : ∀ u v : Fin n, v ∈ graph.adjacency u ↔ G.Adj u v)
    (hn : ∀ u : Fin n, (graph.adjacency u).Nodup) :
    by
      classical
      exact (graph.vertices.map (fun v => (graph.adjacency v).length)).sum =
        2 * G.edgeFinset.card := by
  classical
  have hv : graph.vertices.toFinset = Finset.univ := by
    ext v
    simp [graph.vertices_complete]
  rw [← List.sum_toFinset _ graph.vertices_nodup, hv]
  calc
    ∑ v : Fin n, (graph.adjacency v).length = ∑ v : Fin n, G.degree v :=
      Finset.sum_congr rfl (fun v _ => adjacency_length_degree graph G hadj hn v)
    _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

universe upet1

private lemma worker_edge_inspections {W : Type upet1} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (G : SimpleGraph (Fin n))
    (weight : Sym2 (Fin n) → W) (root : Fin n)
    (hadj : ∀ u v : Fin n, v ∈ graph.adjacency u ↔ G.Adj u v)
    (hn : ∀ u : Fin n, (graph.adjacency u).Nodup) :
    by
      classical
      exact (worker graph weight root).time.2.1 = 2 * G.edgeFinset.card := by
  classical
  rw [worker_inspections graph weight root]
  exact adjacency_sum_twice_edges graph G hadj hn

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

end Cslib.Algorithms.Lean.Prim

namespace Cslib.Algorithms.Lean.Prim

universe u

/-- Each adjacency occurrence is inspected exactly once. -/
public theorem prim_inspections {W : Type u} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    (prim graph weight root).time.2.1 =
      (graph.vertices.map (fun v => (graph.adjacency v).length)).sum :=
  Cslib.Algorithms.Lean.Prim.worker_inspections graph weight root

/-- A key comparison occurs only on a successful membership test. -/
public theorem prim_key_tests_le {W : Type u} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    (prim graph weight root).time.2.2 ≤
      (graph.vertices.map (fun v => (graph.adjacency v).length)).sum := by
  have h := Cslib.Algorithms.Lean.Prim.prim_tests_le_inspections graph weight root
  rw [Cslib.Algorithms.Lean.Prim.worker_inspections graph weight root] at h
  exact h

/-- Every actual heap-event coordinate has the stated logarithmic bound. -/
public theorem prim_heap_time {W : Type u} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    let a := (graph.vertices.map (fun v => (graph.adjacency v).length)).sum
    ∀ c : Fin 5, (prim graph weight root).time.1 c ≤
      20 * (2 * n + a) * (Nat.log2 (n + 1) + 1) + a := by
  dsimp only
  intro c
  have h := Cslib.Algorithms.Lean.Prim.prim_heap_cost graph weight root c
  rw [Cslib.Algorithms.Lean.Prim.worker_inspections graph weight root] at h
  exact h

/-- Exact duplicate-free undirected adjacency gives exactly two inspections per edge. -/
public theorem prim_edge_inspections {W : Type u} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (G : SimpleGraph (Fin n))
    (weight : Sym2 (Fin n) → W) (root : Fin n) : by
    classical
    exact (∀ u v : Fin n, v ∈ graph.adjacency u ↔ G.Adj u v) →
      (∀ u : Fin n, (graph.adjacency u).Nodup) →
      (prim graph weight root).time.2.1 = 2 * G.edgeFinset.card := by
  classical
  intro hadj hn
  exact Cslib.Algorithms.Lean.Prim.worker_edge_inspections graph G weight root hadj hn

end Cslib.Algorithms.Lean.Prim
