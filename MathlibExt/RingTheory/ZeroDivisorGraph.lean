/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- MathlibExt/RingTheory/ZeroDivisorGraph.lean
module
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Combinatorics.SimpleGraph.Basic
/-!
# Zero-divisor graph of a commutative ring

Formalizes the zero-divisor graph from Marco Caoduro and Meike Neuwohner,
[Boxicity and Threshold Dimension of Zero Divisor Graphs](https://arxiv.org/abs/2608.27381v1)
(formalized definition in `boxicity_arxiv.tex` lines 383–390):
vertices are the nonzero zero divisors and two vertices are
adjacent exactly when their product is zero.

The cited paper studies finite nonzero (commutative unital) rings,
while the reusable definition here works generally for any
commutative ring: the construction and proofs below require only
`CommRing R`, with no `Nontrivial R` or `Fintype R` hypotheses.
-/
universe u

@[expose] public section

namespace ZeroDivisorGraph

/-- **Nonzero zero divisors.** For a commutative ring $R$, this is the set of elements
$r \in R$ with $r \neq 0$ such that $sr = 0$ for some nonzero $s \in R$, that is, the nonzero
zero divisors of $R$. They are the vertices of the zero-divisor graph of $R$. -/
public abbrev Vertex (R : Type u) [CommRing R] :
    Type u := { r : R // r ≠ 0 ∧ r ∉ nonZeroDivisors R }

/-- **The zero-divisor graph.** For a commutative ring $R$, the zero-divisor graph of $R$ is
the simple graph whose vertices are the nonzero zero divisors of $R$, in which two distinct
vertices $v$ and $w$ are adjacent exactly when $vw = 0$. -/
public def zeroDivisorGraph (R : Type u) [CommRing R] :
    SimpleGraph (Vertex R) :=
  SimpleGraph.fromRel fun v w : Vertex R => (v : R) * (w : R) = 0

/-- **Vertices are the nonzero zero divisors.** Let $R$ be a commutative ring. An element
$r \in R$ is a vertex of the zero-divisor graph of $R$ if and only if $r \neq 0$ and $r$ is a
zero divisor, that is, $sr = 0$ for some nonzero $s \in R$. -/
public theorem exists_vertex_iff (R : Type u) [CommRing R] (r : R) :
    (∃ v : Vertex R, (v : R) = r) ↔ (r ≠ 0 ∧ r ∉ nonZeroDivisors R) := by
  constructor
  · rintro ⟨v, rfl⟩
    exact v.property
  · rintro ⟨h0, hmem⟩
    exact ⟨⟨r, h0, hmem⟩, rfl⟩

/-- **Adjacency in the zero-divisor graph.** Let $R$ be a commutative ring. Two vertices $v$
and $w$ of the zero-divisor graph of $R$ are adjacent if and only if $v \neq w$ and $vw = 0$. -/
public theorem adj_iff (R : Type u) [CommRing R]
    {v w : Vertex R} :
    (zeroDivisorGraph R).Adj v w ↔ v ≠ w ∧ (v : R) * (w : R) = 0 := by
  unfold zeroDivisorGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, by rw [mul_comm]; exact h⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

end ZeroDivisorGraph
