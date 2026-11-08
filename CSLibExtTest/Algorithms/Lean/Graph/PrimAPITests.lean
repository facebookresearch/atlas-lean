/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Graph.Prim

/-!
# Ordinary Prim public API consumers

Each of the seven general facts is applied at its complete frozen type.
-/

open Cslib.Algorithms.Lean
open scoped BigOperators

universe u

#check @Prim.prim

#check @Prim.prim_root

example {W : Type u} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    (Prim.prim graph weight root).ret[root] = none := by
  exact Prim.prim_root graph weight root

#check @Prim.prim_parent_edge

example {W : Type u} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    ∀ u v : Fin n, (Prim.prim graph weight root).ret[v] = some u →
      v ∈ graph.adjacency u := by
  exact Prim.prim_parent_edge graph weight root

#check @Prim.prim_minimum_spanningTree

example {n : Nat} (graph : DirectedAdjacency (Fin n)) (G : SimpleGraph (Fin n))
    (weight : Sym2 (Fin n) → ℝ) (root : Fin n) : by
    classical
    exact (∀ u v : Fin n, v ∈ graph.adjacency u ↔ G.Adj u v) → G.Connected →
      let parents := (Prim.prim graph weight root).ret
      let T := SimpleGraph.fromRel (fun u v : Fin n => parents[v] = some u)
      T ≤ G ∧ T.IsTree ∧ ∀ H : SimpleGraph (Fin n), H ≤ G → H.IsTree →
        (∑ e ∈ T.edgeFinset, weight e) ≤ ∑ e ∈ H.edgeFinset, weight e := by
  exact Prim.prim_minimum_spanningTree graph G weight root

#check @Prim.prim_inspections

example {W : Type u} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    (Prim.prim graph weight root).time.2.1 =
      (graph.vertices.map (fun v => (graph.adjacency v).length)).sum := by
  exact Prim.prim_inspections graph weight root

#check @Prim.prim_key_tests_le

example {W : Type u} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    (Prim.prim graph weight root).time.2.2 ≤
      (graph.vertices.map (fun v => (graph.adjacency v).length)).sum := by
  exact Prim.prim_key_tests_le graph weight root

#check @Prim.prim_heap_time

example {W : Type u} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Sym2 (Fin n) → W) (root : Fin n) :
    let a := (graph.vertices.map (fun v => (graph.adjacency v).length)).sum
    ∀ c : Fin 5, (Prim.prim graph weight root).time.1 c ≤
      20 * (2 * n + a) * (Nat.log2 (n + 1) + 1) + a := by
  exact Prim.prim_heap_time graph weight root

#check @Prim.prim_edge_inspections

example {W : Type u} [LinearOrder W] [Zero W] {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (G : SimpleGraph (Fin n))
    (weight : Sym2 (Fin n) → W) (root : Fin n) : by
    classical
    exact (∀ u v : Fin n, v ∈ graph.adjacency u ↔ G.Adj u v) →
      (∀ u : Fin n, (graph.adjacency u).Nodup) →
      (Prim.prim graph weight root).time.2.1 = 2 * G.edgeFinset.card := by
  exact Prim.prim_edge_inspections graph G weight root
