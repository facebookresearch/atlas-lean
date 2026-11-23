/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-! # Deza graphs

This module introduces Deza graphs with parameters `(n, k, b, a)`,
following Golubyatnikov (see https://arxiv.org/abs/2608.13089v1, lines 163--164).
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Deza graph.** Let $G$ be a simple graph on a finite vertex set $V$, and let $n, k, b, a$ be
natural numbers. Then $G$ is a Deza graph with parameters $(n, k, b, a)$ when $a \le b \le k < n$,
$V$ has exactly $n$ elements, every vertex of $G$ has degree $k$, and any two distinct vertices of
$G$ have exactly $a$ or exactly $b$ common neighbours, whether or not they are adjacent.

Source: Golubyatnikov, https://arxiv.org/abs/2608.13089v1, lines 163--164. -/
structure IsDezaWith (n k b a : ℕ) : Prop where
  /-- Lower parameter inequality `a ≤ b`. -/
  a_le_b : a ≤ b
  /-- Middle parameter inequality `b ≤ k`. -/
  b_le_k : b ≤ k
  /-- Strict parameter inequality `k < n`. -/
  k_lt_n : k < n
  /-- Exactly `n` vertices. -/
  card_eq : Fintype.card V = n
  /-- `k`-regularity. -/
  regular : G.IsRegularOfDegree k
  /-- Two-valued common-neighbour counts. -/
  common_eq : ∀ u v : V, u ≠ v →
    Fintype.card (G.commonNeighbors u v) = a ∨
      Fintype.card (G.commonNeighbors u v) = b

/-- **Parameter bound $a \le k$ for Deza graphs.** If a finite simple graph $G$ is a Deza graph
with parameters $(n, k, b, a)$, then $a \le k$. -/
theorem IsDezaWith.a_le_k {n k b a : ℕ} (h : G.IsDezaWith n k b a) : a ≤ k :=
  le_trans h.a_le_b h.b_le_k

/-- **Parameter bound $b < n$ for Deza graphs.** If a finite simple graph $G$ is a Deza graph
with parameters $(n, k, b, a)$, then $b < n$. -/
theorem IsDezaWith.b_lt_n {n k b a : ℕ} (h : G.IsDezaWith n k b a) : b < n :=
  lt_of_le_of_lt h.b_le_k h.k_lt_n

/-- **Parameter bound $a < n$ for Deza graphs.** If a finite simple graph $G$ is a Deza graph
with parameters $(n, k, b, a)$, then $a < n$. -/
theorem IsDezaWith.a_lt_n {n k b a : ℕ} (h : G.IsDezaWith n k b a) : a < n :=
  lt_of_le_of_lt h.a_le_k h.k_lt_n

end SimpleGraph
