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
# High-degree vertices of small vertex covers

A vertex of degree more than `k` belongs to every vertex cover of size at most `k`: a cover
that omits a vertex must contain all of its neighbors. This is the observation behind the
high-degree reduction rule used to kernelize vertex cover (M. Cygan, F. V. Fomin, Ł. Kowalik,
D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk, S. Saurabh, *Parameterized Algorithms*,
Springer, 2015, Chapter 2). The reduction rule itself, the kernel, and the bounded search tree
are not formalized here.
-/

@[expose] public section

namespace SimpleGraph

/-- A vertex of degree more than `k` belongs to every vertex cover of size at most `k`, stated
on Mathlib's `SimpleGraph.IsVertexCover`: a cover that omits the vertex must contain all of its
neighbors. -/
theorem mem_of_card_le_of_lt_degree {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (hC : G.IsVertexCover ↑C)
    {k : ℕ} {v : V} (hk : C.card ≤ k) (hdeg : k < G.degree v) :
    v ∈ C := by
  by_contra hv
  have hsub : G.neighborFinset v ⊆ C := by
    intro u hu
    rw [mem_neighborFinset] at hu
    rcases hC hu with h | h
    · rw [Finset.mem_coe] at h
      exact absurd h hv
    · rw [Finset.mem_coe] at h
      exact h
  have hle := Finset.card_le_card hsub
  rw [card_neighborFinset_eq_degree] at hle
  omega

end SimpleGraph

end
