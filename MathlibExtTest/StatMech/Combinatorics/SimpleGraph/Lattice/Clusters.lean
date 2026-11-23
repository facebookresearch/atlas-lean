/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Algebra.BigOperators.Fin

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters`

Computes open edges, open subgraphs, and clusters of `ℤ^d` bond configurations at the two extreme
configurations: with every bond closed the cluster of a site is the site alone, and with every bond
open `openSubgraph` is the whole lattice and the cluster of the origin of `ℤ²` contains `(1, 1)`.
Exhibits the unit square of `ℤ²` as an open circuit (`IsOpenCircuit`) of the all-open
configuration, and checks the equivalence-relation API of `Connected` on it.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.Clusters

open _root_.StatMech _root_.StatMech.Lattice

/-- The configuration with every bond open. -/
def allOpen (d : ℕ) : ConfigSpace (Sym2 (Site d)) := fun _ => true

/-- The configuration with every bond closed. -/
def allClosed (d : ℕ) : ConfigSpace (Sym2 (Site d)) := fun _ => false

-- With every bond open, the open subgraph is the whole lattice.
example (d : ℕ) : openSubgraph d (allOpen d) = hypercubicLattice d := by
  ext x y; simp [openSubgraph_adj, allOpen]

-- With every bond closed, the open subgraph has no edges.
example (d : ℕ) : openSubgraph d (allClosed d) = ⊥ := by
  ext x y; simp [openSubgraph_adj, allClosed]

-- With every bond closed, the cluster of a site is that site alone.
example (d : ℕ) (x : Site d) : cluster d (allClosed d) x = {x} := by
  have h : openSubgraph d (allClosed d) = ⊥ := by
    ext x y; simp [openSubgraph_adj, allClosed]
  ext y
  simp only [mem_cluster, Connected, h, SimpleGraph.reachable_bot, Set.mem_singleton_iff]
  exact eq_comm

-- A single open bond `{0, e₁}` of `ℤ²` is an open edge, so its endpoints are connected.
example : Connected 2 (fun e => decide (e = s(![0, 0], ![1, 0]))) ![0, 0] ![1, 0] :=
  IsOpenEdge.connected ⟨by simp [Fin.sum_univ_two], by simp⟩

-- With every bond open, `(1, 1)` is in the cluster of the origin (via `(1, 0)`).
example : (![1, 1] : Site 2) ∈ cluster 2 (allOpen 2) ![0, 0] := by
  rw [mem_cluster]
  have h1 : Connected 2 (allOpen 2) ![0, 0] ![1, 0] :=
    IsOpenEdge.connected ⟨by simp [Fin.sum_univ_two], rfl⟩
  have h2 : Connected 2 (allOpen 2) ![1, 0] ![1, 1] :=
    IsOpenEdge.connected ⟨by simp [Fin.sum_univ_two], rfl⟩
  exact h1.trans h2

-- Clusters of connected sites coincide.
example : cluster 2 (allOpen 2) ![1, 0] = cluster 2 (allOpen 2) ![0, 0] :=
  cluster_eq_of_connected
    (IsOpenEdge.connected ⟨by simp [Fin.sum_univ_two], rfl⟩ : Connected 2 _ _ _).symm

/-- The unit square `0 → e₁ → e₁ + e₂ → e₂ → 0` as a closed walk in the all-open subgraph. -/
def unitSquare : (openSubgraph 2 (allOpen 2)).Walk ![0, 0] ![0, 0] :=
  .cons (v := ![1, 0]) ⟨by simp [Fin.sum_univ_two], rfl⟩ <|
  .cons (v := ![1, 1]) ⟨by simp [Fin.sum_univ_two], rfl⟩ <|
  .cons (v := ![0, 1]) ⟨by simp [Fin.sum_univ_two], rfl⟩ <|
  .cons ⟨by simp [Fin.sum_univ_two], rfl⟩ .nil

-- The unit square has length four.
example : unitSquare.length = 4 := rfl

-- The unit square is an open circuit (a closed trail with at least one edge).
example : IsOpenCircuit 2 (allOpen 2) unitSquare := by
  refine ⟨⟨?_⟩, ?_⟩
  · unfold unitSquare
    decide
  · nofun

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.Clusters
