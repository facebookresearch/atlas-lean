/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.ConnectedComponents

open Batteries Cslib.Algorithms.Lean

example (n : Nat) (edges : List (Fin n × Fin n)) :
    TimeM (Nat × Nat × Nat) {s : UnionFind // s.size = n} :=
  UnionFind.connectedComponents n edges

example (n : Nat) (edges : List (Fin n × Fin n)) :
    (UnionFind.connectedComponents n edges).ret.val.size = n :=
  UnionFind.connectedComponents_size n edges

example (n : Nat) (edges : List (Fin n × Fin n)) (a b : Fin n) :
    UnionFind.Equiv (UnionFind.connectedComponents n edges).ret.val a.val b.val ↔
      (SimpleGraph.fromEdgeSet {e | e ∈ edges.map (fun p ↦ s(p.1, p.2))}).Reachable a b :=
  UnionFind.connectedComponents_equiv_iff_reachable n edges a b

example (uf : UnionFind) (x y : Fin uf.size) :
    (uf.checkEquiv x y).1.size = uf.size ∧
      ((uf.checkEquiv x y).2 = true ↔ UnionFind.Equiv uf x.val y.val) ∧
      ∀ (a b : Nat), UnionFind.Equiv (uf.checkEquiv x y).1 a b ↔
        UnionFind.Equiv uf a b :=
  UnionFind.checkEquiv_spec uf x y

example (n : Nat) (edges : List (Fin n × Fin n)) :
    let graph : SimpleGraph (Fin n) :=
      SimpleGraph.fromEdgeSet {e | e ∈ edges.map (fun p ↦ s(p.1, p.2))}
    (UnionFind.connectedComponents n edges).time =
      (n, 2 * edges.length, n - Nat.card graph.ConnectedComponent) ∧
    Nat.card graph.ConnectedComponent +
      (UnionFind.connectedComponents n edges).time.2.2 = n ∧
    (0 < n → (UnionFind.connectedComponents n edges).time.2.2 ≤ n - 1) :=
  UnionFind.connectedComponents_time_spec n edges

example : (UnionFind.connectedComponents 0 []).time = (0, 0, 0) := by
  simpa using (UnionFind.connectedComponents_time_spec 0 []).1
