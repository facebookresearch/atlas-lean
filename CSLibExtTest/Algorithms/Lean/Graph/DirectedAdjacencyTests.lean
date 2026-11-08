/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DirectedAdjacencyTests

open DirectedAdjacency

inductive EmptyVertex

private def emptyGraph : DirectedAdjacency EmptyVertex where
  vertices := []
  vertices_nodup := by simp
  vertices_complete vertex := by cases vertex
  adjacency vertex := by cases vertex

example : emptyGraph.vertices = [] := rfl

inductive Solo
  | only
  deriving DecidableEq

private def isolatedGraph : DirectedAdjacency Solo where
  vertices := [.only]
  vertices_nodup := by simp
  vertices_complete vertex := by cases vertex; simp
  adjacency _ := []

example : isolatedGraph.Reachable .only .only :=
  Relation.ReflTransGen.refl

example : Walk isolatedGraph 0 Solo.only Solo.only :=
  Relation.RelatesInSteps.refl Solo.only

example : ¬isolatedGraph.Edge .only .only := by
  simp [DirectedAdjacency.Edge, isolatedGraph]

inductive Vertex
  | a
  | b
  | c
  | d
  deriving DecidableEq

open Vertex

private def graph : DirectedAdjacency Vertex where
  vertices := [a, b, c, d]
  vertices_nodup := by decide
  vertices_complete vertex := by cases vertex <;> simp
  adjacency
    | a => [b, b]
    | b => [c]
    | c => [c]
    | d => []

example : graph.Edge c c := by
  simp [DirectedAdjacency.Edge, graph]

example : Walk graph 1 c c :=
  Relation.RelatesInSteps.single (by simp [DirectedAdjacency.Edge, graph])

example : graph.adjacency a = [b, b] := rfl

example : graph.Edge a b ∧ ¬graph.Edge b a := by
  simp [DirectedAdjacency.Edge, graph]

example : Walk graph 2 a c := by
  exact Relation.RelatesInSteps.tail a b c 1
    (Relation.RelatesInSteps.single
      (show graph.Edge a b by simp [DirectedAdjacency.Edge, graph]))
    (show graph.Edge b c by simp [DirectedAdjacency.Edge, graph])

example : ¬Walk graph 1 a c := by
  rw [walk_succ_iff]
  rintro ⟨next, edge, walk⟩
  rw [walk_zero_iff] at walk
  subst next
  simp [DirectedAdjacency.Edge, graph] at edge

example : ¬graph.Reachable d a := by
  rw [reachable_iff_exists_walk]
  rintro ⟨walkLength, walk⟩
  cases walkLength with
  | zero =>
      rw [walk_zero_iff] at walk
      cases walk
  | succ walkLength =>
      rw [walk_succ_iff] at walk
      obtain ⟨next, edge, _⟩ := walk
      simp [DirectedAdjacency.Edge, graph] at edge

example : (graph.transpose).Edge b a ↔ graph.Edge a b :=
  edge_transpose

example : SemanticallyEquivalent graph.transpose.transpose graph :=
  semanticEquivalent_transpose_transpose

example : graph.transpose.vertices = [a, b, c, d] := rfl

example : graph.transpose.adjacency a = [] := rfl

example : graph.transpose.adjacency b = [a] := rfl

example : graph.transpose.adjacency c = [b, c] := rfl

example : graph.transpose.adjacency d = [] := rfl

example : graph.transpose.transpose.adjacency a = [b] := rfl

private def reorderedGraph : DirectedAdjacency Vertex where
  vertices := [d, c, b, a]
  vertices_nodup := by decide
  vertices_complete vertex := by cases vertex <;> simp
  adjacency := graph.adjacency

example : reorderedGraph.transpose.adjacency c = [c, b] := rfl

example : graph.toDigraph.Adj a b ↔ graph.Edge a b := toDigraph_adj

example : Walk graph 2 a c ↔ Relation.RelatesInSteps graph.Edge a c 2 :=
  Iff.rfl

example : graph.Reachable a c ↔ ∃ walkLength, Walk graph walkLength a c :=
  reachable_iff_exists_walk

example : graph.Reachable a c ↔ Relation.ReflTransGen graph.Edge a c :=
  reachable_iff_reflTransGen

example : graph.Reachable a c ↔ (∃ labels, graph.toLTS.MTr a labels c) := reachable_iff_lts

example : (∃ walkLength, Walk graph walkLength a c) ↔ (∃ labels, graph.toLTS.MTr a labels c) :=
  reachable_iff_exists_walk.symm.trans reachable_iff_lts

example : (∃ walkLength, Walk graph walkLength a c) ↔
    Relation.ReflTransGen graph.Edge a c :=
  reachable_iff_exists_walk.symm.trans reachable_iff_reflTransGen

example : Relation.ReflTransGen graph.Edge a c ↔ (∃ labels, graph.toLTS.MTr a labels c) :=
  reachable_iff_reflTransGen.symm.trans reachable_iff_lts

example : Walk graph.transpose.transpose 2 a c ↔ Walk graph 2 a c :=
  semanticEquivalent_transpose_transpose.walk_iff

example : graph.transpose.transpose.Reachable a c ↔ graph.Reachable a c :=
  semanticEquivalent_transpose_transpose.reachable_iff

example :
    (∃ walkLength, Walk graph walkLength a c) ∧
      Relation.ReflTransGen graph.Edge a c ∧
      (∃ labels, graph.toLTS.MTr a labels c) := by
  have walk : Walk graph 2 a c := by
    exact Relation.RelatesInSteps.tail a b c 1
      (Relation.RelatesInSteps.single
        (show graph.Edge a b by simp [DirectedAdjacency.Edge, graph]))
      (show graph.Edge b c by simp [DirectedAdjacency.Edge, graph])
  have reachable : graph.Reachable a c :=
    reachable_iff_exists_walk.mpr ⟨2, walk⟩
  exact ⟨⟨2, walk⟩, reachable_iff_reflTransGen.mp reachable,
    reachable_iff_lts.mp reachable⟩

end Cslib.Algorithms.Lean.DirectedAdjacencyTests
