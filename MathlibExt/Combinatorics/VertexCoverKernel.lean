/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Card

/-!
# Vertex-cover kernel rule

A vertex of degree more than `k` belongs to every vertex
cover of size at most `k`: otherwise all its neighbors
would have to be in the cover. This is the basic
kernelization rule for vertex cover; the bounded search
tree is not included here.
-/

@[expose] public section

/-- Vertex-cover kernel rule (core of MOD-67), stated on
Mathlib's `SimpleGraph.IsVertexCover`: a vertex of degree
more than `k` belongs to every vertex cover of size at
most `k`. -/
theorem mem_of_degree_lt_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (hC : G.IsVertexCover ↑C)
    {k : ℕ} {v : V} (hk : C.card ≤ k) (hdeg : k < (G.neighborFinset v).card) :
    v ∈ C := by
  by_contra hv
  have hsub : G.neighborFinset v ⊆ C := by
    intro u hu
    rw [SimpleGraph.mem_neighborFinset] at hu
    rcases hC hu with h | h
    · rw [Finset.mem_coe] at h
      exact absurd h hv
    · rw [Finset.mem_coe] at h
      exact h
  have hle := Finset.card_le_card hsub
  omega

end
