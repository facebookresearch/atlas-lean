/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace MetaMathlibExt

/-- **Linear partition of a graph.** Let $G$ be a simple graph on a vertex type $V$ and let $k$
be a natural number. A $k$-linear partition of $G$ is a set of exactly $k$ blocks, each block a
nonempty finite sequence of pairwise distinct vertices, such that every vertex of $G$ lies in
exactly one block and any two consecutive vertices of a block are nonadjacent in $G$. The
blocks themselves are unordered; only the vertices within a block are ordered.

Source: Gonzales, JIS VOL25, concept `jis_term_096dd7cbe3f83bcfea2406a6`,
`https://cs.uwaterloo.ca/journals/JIS/VOL25/Gonzales/gonzales2.tex`. -/
structure LinearPartition {V : Type*} [DecidableEq V] (G : SimpleGraph V) (k : ℕ) where
  blocks : Finset (List V)
  card_eq : blocks.card = k
  nonempty : ∀ L ∈ blocks, L ≠ []
  nodup : ∀ L ∈ blocks, L.Nodup
  covers : ∀ v : V, ∃! L, L ∈ blocks ∧ v ∈ L
  consecutive : ∀ L ∈ blocks, List.IsChain (fun a b => ¬G.Adj a b) L

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}

@[ext]
theorem LinearPartition.ext {P Q : LinearPartition G k}
    (h : P.blocks = Q.blocks) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

theorem LinearPartition.existsUniqueBlock (P : LinearPartition G k) (v : V) :
    ∃! L, L ∈ P.blocks ∧ v ∈ L :=
  P.covers v

theorem LinearPartition.consecutive_mem (P : LinearPartition G k) {L : List V}
    (hL : L ∈ P.blocks) : List.IsChain (fun a b => ¬G.Adj a b) L :=
  P.consecutive L hL

end MetaMathlibExt

end
