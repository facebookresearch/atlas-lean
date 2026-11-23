/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Clique

open scoped symmDiff

/-!
# Finite simplex graphs

Finite simplex graph construction following Huang, Xie, Xu arXiv:2608.25416v1 lines 193-197.
Vertices are the cliques of the base graph; two vertices are adjacent when their
symmetric difference has cardinality one.
The construction conservatively generalizes the cited finite-graph definition
by omitting Fintype; finiteness is not needed for the adjacency API.
-/

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

@[expose]
public section

/-- **Simplex vertices.** Let $G$ be a simple graph on a vertex type $V$. A simplex vertex
of $G$ is a finite set $s$ of vertices that is a clique of $G$, meaning that any two distinct
elements of $s$ are adjacent in $G$. -/
public def SimplexVertex := { s : Finset V // G.IsClique (↑s : Set V) }

/-- **Empty simplex vertex.** Let $G$ be a simple graph. The empty simplex vertex of $G$ is
the empty set of vertices, which is a clique of $G$. -/
public def emptyVertex : SimplexVertex G := ⟨∅, by simp⟩

/-- **Singleton simplex vertex.** Let $G$ be a simple graph. For a vertex $v$ of $G$, the
singleton simplex vertex of $v$ is the one-element set containing $v$, which is a clique of
$G$. -/
public def singletonVertex (v : V) : SimplexVertex G := ⟨{v}, by simp⟩

/-- **Simplex graph.** Let $G$ be a simple graph. The simplex graph of $G$ is the simple graph
whose vertices are the simplex vertices of $G$ (the finite cliques of $G$), in which two cliques
$s$ and $t$ are adjacent exactly when their symmetric difference $s \triangle t$ has exactly one
element.

The vertex type of $G$ is not required to be finite. -/
public def simplexGraph : SimpleGraph (SimplexVertex G) where
  Adj x y := (x.val ∆ y.val).card = 1
  symm := ⟨by
    intro x y h
    simpa only [symmDiff_comm] using h⟩
  loopless := ⟨by
    intro x h
    rw [Finset.symmDiff_def] at h
    simp at h⟩

/-- **Adjacency in the simplex graph.** Let $G$ be a simple graph. Two simplex vertices $s$ and
$t$ of $G$ are adjacent in the simplex graph of $G$ if and only if their symmetric difference
$s \triangle t$ has exactly one element. -/
public theorem adj_iff (x y : SimplexVertex G) :
    (simplexGraph G).Adj x y ↔ (x.val ∆ y.val).card = 1 := Iff.rfl

/-- **The empty clique is adjacent to every singleton.** Let $G$ be a simple graph. For every
vertex $v$ of $G$, the empty simplex vertex of $G$ and the singleton simplex vertex of $v$ are
adjacent in the simplex graph of $G$. -/
public theorem empty_adj_singleton (v : V) :
    (simplexGraph G).Adj (emptyVertex G) (singletonVertex G v) := by
  change ((∅ : Finset V) ∆ ({v} : Finset V)).card = 1
  rw [Finset.symmDiff_def]
  simp

end

end SimpleGraph
