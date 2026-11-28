/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Snort, oppositions, and almost opposable graphs

Statements from Rylo Ashmore, Beth Ann Austin, Alfie M. Davies, Danny Dyer, and
William Kellough, "On Graph Automorphisms Related to SNORT", *INTEGERS* 26
(2026), Article G2 (arXiv:2506.20669).

Snort on a finite simple graph: the players alternately colour an uncoloured
vertex that is not adjacent to a vertex coloured by the opponent; a player with
no legal move loses. Since the rules are symmetric, `snortMoverWins G k mine
theirs` (defined in
`MathlibExt.GraphTheory.SnortOppositionsExistsLargeTreeSnortSecondPlayerWins`)
records whether the player to move (owning `mine`) wins, with `k` a
fuel bound on the number of remaining moves; at fuel `Fintype.card V` from the
empty position the fuel never runs out, so `SnortFirstPlayerWins` and
`SnortSecondPlayerWins` (the latter also defined in
`MathlibExt.GraphTheory.SnortOppositionsExistsLargeTreeSnortSecondPlayerWins`)
are the outcomes of the game on the untinted graph. The `n`-firework `firework G u v n`
is defined in that module too.

An *opposition* of `G` is an involutive automorphism `f` with `f v ∉ N[v]`
for all `v`; `G` is *opposable* if it has one. A set `S` is *admissible* if
`u ∈ S ⊆ N[u]` for some `u`, and `G` is *almost opposable* if `G - S` is
opposable for an admissible `S`. "Order two" is read as involutive (`f ∘ f =
id`), which only differs on the empty graph.

Graph products given by a formula `φ(g₁g₂ ∈ E(G), h₁h₂ ∈ E(H), g₁ = g₂, h₁ =
h₂)` are `formulaProduct φ G H`, with `φ` a Boolean function of the four atoms
(every formula in the paper's connectives is one) and loops discarded as in a
simple graph. Grids and chessboard graphs are defined directly by adjacency of
coordinates.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Fintype.Pi
public import MathlibExt.Combinatorics.SimpleGraph.CompatibleOppositionProducts
public import MathlibExt.Combinatorics.SimpleGraph.RookGraph
public import MathlibExt.Combinatorics.SimpleGraph.SnortOppositions
public import MathlibExt.Combinatorics.SimpleGraph.StrongGridOpposability
public import MathlibExt.GameTheory.SnortOppositionStrategy
public import MathlibExt.GraphTheory.SnortOppositionsExistsLargeTreeSnortSecondPlayerWins

namespace MetaMathlibExt

@[expose] public section

variable {V W : Type*}

/-- **First player wins Snort.** Let $G$ be a finite simple graph. In Snort on $G$ the two players
alternately colour a vertex that is not yet coloured and is not adjacent to any vertex coloured
by the opponent, and a player with no legal move loses. The first player wins Snort on $G$ when
the player who moves first has a winning strategy from the position in which no vertex is
coloured.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 1. -/
def SnortFirstPlayerWins [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  snortMoverWins G (Fintype.card V) ∅ ∅ = true

/-- **Snort response pairs.** In Snort on a finite graph $G$, a pair $(u, v)$ of vertices is a
response pair if $u \neq v$, $u$ and $v$ are not adjacent (so the first player colouring $u$ and
the second answering $v$ is legal), and the first player, now to move, loses from the position
in which the first player has coloured $u$ and the second player has coloured $v$.

The outcome is computed with a bound of $|V(G)| - 2$ further moves, the number of uncoloured
vertices, so the bound never cuts the game short.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 3 (response
pair). -/
def IsSnortResponsePair [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : Prop :=
  u ≠ v ∧ ¬ G.Adj u v ∧ snortMoverWins G (Fintype.card V - 2) {u} {v} = false

/-- **Cartesian grid.** For $k \in \mathbb{N}$ and side lengths $n_1, \dots, n_k \in \mathbb{N}$,
the $k$-dimensional Cartesian grid has as vertices the tuples $(x_1, \dots, x_k)$ of integers
with $0 \le x_i < n_i$ for each $i$, and two tuples are adjacent when they differ in exactly one
coordinate, and there by exactly one. It is the Cartesian product
$P_{n_1} \square \cdots \square P_{n_k}$ of the paths $P_{n_i}$ on $n_i$ vertices.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Corollary 4 (Cartesian
grids). -/
def cartesianGrid {k : ℕ} (n : Fin k → ℕ) : SimpleGraph ((i : Fin k) → Fin (n i)) :=
  SimpleGraph.fromRel fun x y => ∃ i, (x i : ℕ) + 1 = y i ∧ ∀ j, j ≠ i → x j = y j

instance {k : ℕ} (n : Fin k → ℕ) : DecidableRel (cartesianGrid n).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ _))

/-- **King's graph.** For natural numbers $n$ and $m$, the king's graph of the $n \times m$
board is the simple graph whose vertices are the pairs $(i, j)$ with $0 \le i < n$ and
$0 \le j < m$, in which two distinct pairs $(i, j)$ and $(i', j')$ are adjacent when
$|i - i'| \le 1$ and $|j - j'| \le 1$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 5. -/
def kingGraph (n m : ℕ) : SimpleGraph (Fin n × Fin m) :=
  SimpleGraph.fromRel fun x y => |(x.1 : ℤ) - y.1| ≤ 1 ∧ |(x.2 : ℤ) - y.2| ≤ 1

instance (n m : ℕ) : DecidableRel (kingGraph n m).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ _))

/-- **Knight's graph.** For natural numbers $n$ and $m$, the knight's graph of the $n \times m$
board is the simple graph whose vertices are the pairs $(i, j)$ with $0 \le i < n$ and
$0 \le j < m$, in which two pairs $(i, j)$ and $(i', j')$ are adjacent when either
$|i - i'| = 1$ and $|j - j'| = 2$, or $|i - i'| = 2$ and $|j - j'| = 1$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 5 (proof of
Theorem 9). -/
def knightGraph (n m : ℕ) : SimpleGraph (Fin n × Fin m) :=
  SimpleGraph.fromRel fun x y =>
    (|(x.1 : ℤ) - y.1| = 1 ∧ |(x.2 : ℤ) - y.2| = 2) ∨
      (|(x.1 : ℤ) - y.1| = 2 ∧ |(x.2 : ℤ) - y.2| = 1)

instance (n m : ℕ) : DecidableRel (knightGraph n m).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ _))

/-- **Bishop's graph.** For natural numbers $n$ and $m$, the bishop's graph on the $n \times m$
board has as vertices the cells $(i, j)$ with $0 \le i < n$ and $0 \le j < m$, and two distinct
cells $(i, j)$ and $(i', j')$ are adjacent when they lie on a common diagonal, that is, when
$|i - i'| = |j - j'|$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 5 (proof of
Theorem 10). -/
def bishopGraph (n m : ℕ) : SimpleGraph (Fin n × Fin m) :=
  SimpleGraph.fromRel fun x y => |(x.1 : ℤ) - y.1| = |(x.2 : ℤ) - y.2|

instance (n m : ℕ) : DecidableRel (bishopGraph n m).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ _))

/-- **Queen's graph.** For natural numbers $n$ and $m$, the queen's graph of the $n \times m$
board is the simple graph whose vertices are the pairs $(i, j)$ with $0 \le i < n$ and
$0 \le j < m$, in which two distinct pairs $(i, j)$ and $(i', j')$ are adjacent when $i = i'$,
or $j = j'$, or $|i - i'| = |j - j'|$; that is, when they share a row, a column or a diagonal.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 5. -/
def queenGraph (n m : ℕ) : SimpleGraph (Fin n × Fin m) :=
  SimpleGraph.fromRel fun x y =>
    x.1 = y.1 ∨ x.2 = y.2 ∨ |(x.1 : ℤ) - y.1| = |(x.2 : ℤ) - y.2|

instance (n m : ℕ) : DecidableRel (queenGraph n m).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ _))

instance (n m : ℕ) : DecidableRel (SimpleGraph.rookGraph n m).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ _))

/-- **Snort on two vertices.** The first player wins Snort on the complete graph $K_2$, and
the second player wins Snort on the graph with two vertices and no edges.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 1; characteristic
check of `snortMoverWins`. -/
theorem snort_two_vertices :
    SnortFirstPlayerWins (⊤ : SimpleGraph (Fin 2)) ∧
      SnortSecondPlayerWins (⊥ : SimpleGraph (Fin 2)) := by
  unfold SnortFirstPlayerWins SnortSecondPlayerWins; decide

/-- **Snort on the $2 \times 2$ queen's and rook's graphs.** The first player wins Snort on
the queen's graph of the $2 \times 2$ board (the Peaceable Queens game), and the second
player wins Snort on the rook's graph of the $2 \times 2$ board (the Peaceable Rooks game).

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 5; characteristic
check of `queenGraph` and `SimpleGraph.rookGraph`. -/
theorem snort_two_by_two :
    SnortFirstPlayerWins (queenGraph 2 2) ∧ SnortSecondPlayerWins (SimpleGraph.rookGraph 2 2) := by
  unfold SnortFirstPlayerWins SnortSecondPlayerWins; decide

/-- **Fireworks preserve second-player wins in Snort.** Let $G$ be a finite simple graph and let
$(u, v)$ be a response pair of $G$ whose distance in $G$ is at least $3$ (infinite distance,
when $u$ and $v$ lie in different components, is allowed). If the second player wins Snort on
$G$, then for every natural number $n$ at least the number $|V(G)|$ of vertices of $G$, the
second player wins Snort on the $n$-firework of $G$ at $(u, v)$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 4. -/
public theorem_wanted snortSecondPlayerWins_firework [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (hG : SnortSecondPlayerWins G)
    (huv : IsSnortResponsePair G u v) (hdist : 3 ≤ G.edist u v) (n : ℕ)
    (hn : Fintype.card V ≤ n) [DecidableRel (firework G u v n).Adj] :
    SnortSecondPlayerWins (firework G u v n)

/-- **Almost opposable graphs are first-player wins in Snort.** For every finite simple graph $G$
that is almost opposable, the first player wins Snort on $G$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Lemma 3. -/
public theorem_wanted snortFirstPlayerWins_of_isAlmostOpposable [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : IsAlmostOpposable G) : SnortFirstPlayerWins G

/-- **Cartesian products of compatibly almost opposable graphs.** Let $G$ and $H$ be compatibly
almost opposable graphs. Suppose that for some vertex $u$ of $G$ there are an involutive
automorphism $\alpha$ of $G$ and an opposition $f$ of the induced subgraph $G - u$ on the vertices
other than $u$ such that $\alpha(x) = f(x)$ for every vertex $x \neq u$. Then the Cartesian product
$G \square H$ is compatibly almost opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 7. -/
public theorem_wanted isCompatiblyAlmostOpposable_boxProd (G : SimpleGraph V)
    (H : SimpleGraph W) (hG : IsCompatiblyAlmostOpposable G) (hH : IsCompatiblyAlmostOpposable H)
    (hu : ∃ u : V, ∃ α : G ≃g G, (∀ v, α (α v) = v) ∧
      ∃ f : G.induce ({u}ᶜ : Set V) ≃g G.induce ({u}ᶜ : Set V),
        IsOpposition _ f ∧ ∀ x : ↥({u}ᶜ : Set V), α x = (f x : V)) :
    IsCompatiblyAlmostOpposable (G □ H)

/-- **Opposability of Cartesian grids.** Let $k \ge 1$ and $n_1, \dots, n_k \ge 1$, and let
$G = P_{n_1} \square \cdots \square P_{n_k}$ be the $k$-dimensional Cartesian grid, the Cartesian
product of the paths $P_{n_i}$ on $n_i$ vertices. Then $G$ is almost opposable if and only if at
most one of $n_1, \dots, n_k$ is even, and $G$ is opposable if more than one of them is even.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Corollary 4. -/
public theorem_wanted cartesianGrid_opposability {k : ℕ} (hk : 1 ≤ k) (n : Fin k → ℕ)
    (hn : ∀ i, 1 ≤ n i) :
    (IsAlmostOpposable (cartesianGrid n) ↔ (Finset.univ.filter fun i => Even (n i)).card ≤ 1) ∧
      (1 < (Finset.univ.filter fun i => Even (n i)).card → IsOpposable (cartesianGrid n))

/-- **First player wins Peaceable Kings.** For all natural numbers $n \ge 1$ and $m \ge 1$, the
first player wins Snort on the king's graph of the $n \times m$ board (the Peaceable Kings game).

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 8. -/
public theorem_wanted snortFirstPlayerWins_kingGraph (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    SnortFirstPlayerWins (kingGraph n m)

/-- **Snort on the knight's graph.** For natural numbers $n \ge 1$ and $m \ge 1$, the
second player wins Snort on the knight's graph of the $n \times m$ board (the Peaceable
Knights game) if and only if $n$ is even or $m$ is even.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 9. -/
public theorem_wanted snortSecondPlayerWins_knightGraph_iff (n m : ℕ) (hn : 1 ≤ n)
    (hm : 1 ≤ m) : SnortSecondPlayerWins (knightGraph n m) ↔ Even n ∨ Even m

/-- **Second player wins Peaceable Bishops exactly when a side is even.** For all natural numbers
$n \ge 1$ and $m \ge 1$, the second player wins Snort on the bishop's graph of the $n \times m$
board (the Peaceable Bishops game) if and only if $n$ or $m$ is even.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 10. -/
public theorem_wanted snortSecondPlayerWins_bishopGraph_iff (n m : ℕ) (hn : 1 ≤ n)
    (hm : 1 ≤ m) : SnortSecondPlayerWins (bishopGraph n m) ↔ Even n ∨ Even m

/-- **Snort on the rook's graph.** For natural numbers $n \ge 1$ and $m \ge 1$, the
second player wins Snort on the rook's graph of the $n \times m$ board (the Peaceable
Rooks game) if and only if $n$ and $m$ are both even.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 11. -/
public theorem_wanted snortSecondPlayerWins_rookGraph_iff (n m : ℕ) (hn : 1 ≤ n)
    (hm : 1 ≤ m) : SnortSecondPlayerWins (SimpleGraph.rookGraph n m) ↔ Even n ∧ Even m

/-- **First player wins Peaceable Queens on boards with an odd side.** Let $n \ge 1$ and
$m \ge 1$ be natural numbers such that $n$ or $m$ is odd. Then the first player wins Snort on the
queen's graph of the $n \times m$ board (the Peaceable Queens game).

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 12. -/
public theorem_wanted snortFirstPlayerWins_queenGraph (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h : Odd n ∨ Odd m) : SnortFirstPlayerWins (queenGraph n m)

end

end MetaMathlibExt
