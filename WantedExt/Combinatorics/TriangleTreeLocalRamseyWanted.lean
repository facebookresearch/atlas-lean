/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ramsey hosts locally given by trees of triangles

`AIM-COMBINATORICS-0056` (AIM Graph Ramsey theory, Local trees of
triangles, Rodl): for every `ℓ`, does there exist `G →₂ K₃` which on
every `ℓ` vertices induces a subgraph of a tree of triangles?
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fintype.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.TriangleTreeLocalRamseyWanted

/-- **Trees of triangles.** The trees of triangles on a vertex set $V$ are the graphs on $V$
built recursively as follows. A graph whose edges are exactly the three edges of a triangle on
distinct vertices $a, b, c$ is a tree of triangles. If $H_0$ is a tree of triangles, $xy$ is an
edge of $H_0$, and $z$ is a vertex different from $x$ and $y$ with no neighbours in $H_0$, then
the graph obtained from $H_0$ by joining $z$ to $x$ and to $y$ is a tree of triangles.

Source: AIM-COMBINATORICS-0056, aim-combinatorics-notes.json notes[55]:
any graph built recursively by starting with a triangle, and then adding two
edges at a time that forms a single new triangle with an existing edge. -/
inductive IsTriangleTree {V : Type*} : SimpleGraph V → Prop where
  | base : ∀ (H : SimpleGraph V) (a b c : V),
      a ≠ b → b ≠ c → a ≠ c →
      H.Adj a b → H.Adj b c → H.Adj a c →
      (∀ x y : V, H.Adj x y →
        (x = a ∨ x = b ∨ x = c) ∧ (y = a ∨ y = b ∨ y = c)) →
      (∀ x y : V, (x = a ∨ x = b ∨ x = c) →
        (y = a ∨ y = b ∨ y = c) → x ≠ y → H.Adj x y) →
      IsTriangleTree H
  | step : ∀ (H₀ H : SimpleGraph V) (z x y : V),
      IsTriangleTree H₀ →
      H₀.Adj x y → x ≠ y → z ≠ x → z ≠ y →
      (¬ ∃ w : V, H₀.Adj z w) →
      H.Adj x z → H.Adj y z →
      (∀ w : V, H.Adj z w → w = x ∨ w = y) →
      (∀ u v : V, u ≠ z → v ≠ z → (H.Adj u v ↔ H₀.Adj u v)) →
      IsTriangleTree H

/-- **Graphs that arrow the triangle.** A graph $G$ arrows the triangle in two colours, written
$G \to_2 K_3$, if every colouring of the edges of $G$ with two colours contains a monochromatic
triangle: three distinct pairwise adjacent vertices whose three edges all have the same colour.

Source: AIM-COMBINATORICS-0056, aim-combinatorics-notes.json notes[55]:
`G` with `2` colors arrows `K₃`, i.e. every 2-coloring of the edges of `G`
contains a monochromatic triangle. -/
def Ramseys2Triangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ χ : ∀ (x y : V), G.Adj x y → Fin 2,
    (∀ (x y : V) (h₁ : G.Adj x y) (h₂ : G.Adj y x), χ x y h₁ = χ y x h₂) →
    ∃ a b c : V, ∃ (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c),
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ χ a b hab = χ b c hbc ∧ χ a b hab = χ a c hac

/-- **Graphs that are locally trees of triangles.** A graph $G$ on a vertex set $V$ is locally a
tree of triangles on $\ell$ vertices if for every set $S$ of exactly $\ell$ vertices there is a
tree of triangles on $V$ that contains every edge of $G$ with both endpoints in $S$.

Source: AIM-COMBINATORICS-0056, aim-combinatorics-notes.json notes[55]:
on every `ℓ` vertices `G` induces a subgraph of a tree of triangles. -/
@[nolint unusedArguments]
def IsLocallyTriangleTree {V : Type*} [DecidableEq V] (G : SimpleGraph V) (ℓ : ℕ) : Prop :=
  ∀ S : Finset V, S.card = ℓ →
    ∃ H' : SimpleGraph V, IsTriangleTree H' ∧
      ∀ x y : V, x ∈ S → y ∈ S → G.Adj x y → H'.Adj x y

/-- **Rödl's question on Ramsey graphs that are locally trees of triangles.** This is the
statement that for every natural number $\ell$ there is a finite graph $G$ with at least $\ell$
vertices such that $G \to_2 K_3$ (every colouring of the edges of $G$ with two colours contains
a monochromatic triangle) and $G$ is locally a tree of triangles on $\ell$ vertices: for every
set $S$ of exactly $\ell$ vertices of $G$, some tree of triangles on the vertex set of $G$
contains every edge of $G$ with both endpoints in $S$.

Posed as an open question, it has been answered in the affirmative.

Source: AIM-COMBINATORICS-0056, aim-combinatorics-notes.json notes[55]:
for every `ℓ`, does there exist a graph `G →₂ K₃` which on every `ℓ` vertices
induces a subgraph of a tree of triangles. -/
def conjecture : Prop :=
  ∀ ℓ : ℕ, ∃ (V : Type), ∃ (_ : DecidableEq V), ∃ (_ : Fintype V),
    ∃ G : SimpleGraph V, ℓ ≤ Fintype.card V ∧ Ramseys2Triangle G ∧ IsLocallyTriangleTree G ℓ

/--
**Ramsey graphs for the triangle that are locally trees of triangles.** For every natural number
$\ell$ there is a finite graph $G$ with at least $\ell$ vertices such that $G \to_2 K_3$, that is,
every colouring of the edges of $G$ with two colours contains a monochromatic triangle, and such
that for every set $S$ of exactly $\ell$ vertices of $G$, some tree of triangles on the vertex set
of $G$ contains every edge of $G$ with both endpoints in $S$.

This follows from Reiher and Rödl's girth Ramsey theorem (Theorem 1.6 with $F = K_3$, $r = 2$,
$n = \ell$), which gives a graph $H$ with $H \to_2 K_3$ in which every set of at most $\ell$
vertices induces a partial $K_3$-forest; such graphs have treewidth at most $2$, hence lie in
trees of triangles ($2$-trees).

Source: C. Reiher and V. Rödl, The girth Ramsey theorem,
arXiv:2308.15589, https://arxiv.org/abs/2308.15589. Moved from
`OpenConjectures/Combinatorics/TriangleTreeLocalRamsey`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.TriangleTreeLocalRamseyWanted
