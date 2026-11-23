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
theirs` records whether the player to move (owning `mine`) wins, with `k` a
fuel bound on the number of remaining moves; at fuel `Fintype.card V` from the
empty position the fuel never runs out, so `SnortFirstPlayerWins` and
`SnortSecondPlayerWins` are the outcomes of the game on the untinted graph.

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
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import Mathlib.Data.Fintype.Pi
public import MathlibExt.Combinatorics.SimpleGraph.RookGraph

namespace MetaMathlibExt

@[expose] public section

variable {V W : Type*}

/-- **Snort positions with a move bound.** Let $G$ be a finite simple graph, let $k$ be a natural
number, and let $A$ and $B$ be finite sets of vertices of $G$, the vertices coloured so far by
the player to move and by the opponent. A legal move colours a vertex $v$ that lies in neither
$A$ nor $B$ and has no neighbour in $B$. With move bound $0$ the player to move loses. With move
bound $k + 1$ the player to move wins at $(A, B)$ exactly when some legal move $v$ leaves a
position $(B, A \cup \{v\})$ that the opponent, now to move with move bound $k$, does not win.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 1 (rules of
Snort). -/
def snortMoverWins [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ℕ → Finset V → Finset V → Bool
  | 0, _, _ => false
  | k + 1, mine, theirs =>
      decide (∃ v : V, v ∉ mine ∧ v ∉ theirs ∧ (∀ w ∈ theirs, ¬ G.Adj v w) ∧
        snortMoverWins G k theirs (insert v mine) = false)

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

/-- **Second-player win in Snort.** Let $G$ be a finite simple graph. In Snort on $G$, two
players alternately colour a vertex of $G$ that is not yet coloured, each with their own
colour, and a player may not colour a vertex adjacent to a vertex of the opponent's colour; a
player with no legal move loses. The second player wins Snort on $G$ if, starting from the
position in which no vertex is coloured, the player who moves first has no winning strategy.

Every move colours a new vertex, so the game ends after at most $|V(G)|$ moves and has no
draws; hence this says that the second player has a winning strategy.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 1. -/
def SnortSecondPlayerWins [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  snortMoverWins G (Fintype.card V) ∅ ∅ = false

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

/-- **Oppositions.** An opposition of a graph $G$ is an automorphism $f$ of $G$ such that for
every vertex $v$, $f(f(v)) = v$, $f(v) \neq v$, and $f(v)$ is not adjacent to $v$; that is, an
involutive automorphism moving every vertex outside its closed neighbourhood.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 1 (after
Kakihara). -/
def IsOpposition (G : SimpleGraph V) (f : G ≃g G) : Prop :=
  ∀ v, f (f v) = v ∧ f v ≠ v ∧ ¬ G.Adj v (f v)

/-- **Opposable graphs.** A graph $G$ is opposable if it has an opposition: an automorphism $f$
of $G$ such that for every vertex $v$, $f(f(v)) = v$, $f(v) \neq v$, and $f(v)$ is not adjacent
to $v$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 1. -/
def IsOpposable (G : SimpleGraph V) : Prop :=
  ∃ f : G ≃g G, IsOpposition G f

/-- **Almost opposable graph.** A graph $G$ is almost opposable if there are a vertex $u$ and a
set $S$ of vertices with $u \in S \subseteq N[u]$, where $N[u]$ is the closed neighbourhood of $u$
($u$ together with its neighbours), such that the subgraph $G - S$ induced on the vertices
outside $S$ is opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 4 (almost opposable graphs). -/
def IsAlmostOpposable (G : SimpleGraph V) : Prop :=
  ∃ u : V, ∃ S : Set V, u ∈ S ∧ S ⊆ insert u (G.neighborSet u) ∧ IsOpposable (G.induce Sᶜ)

/-- **Compatibly almost opposable graphs.** A graph $G$ is compatibly almost opposable if there
are a vertex $u$, a set $S$ of vertices with $u \in S \subseteq N[u]$ (the closed neighbourhood
of $u$), an automorphism $\alpha$ of $G$ with $\alpha(\alpha(v)) = v$ for every vertex $v$, and
an opposition $f$ of the subgraph $G - S$ induced on the vertices outside $S$, such that
$\alpha(x) = f(x)$ for every vertex $x \notin S$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 4 (compatibly almost opposable
graphs). -/
def IsCompatiblyAlmostOpposable (G : SimpleGraph V) : Prop :=
  ∃ u : V, ∃ S : Set V, u ∈ S ∧ S ⊆ insert u (G.neighborSet u) ∧
    ∃ α : G ≃g G, (∀ v, α (α v) = v) ∧
      ∃ f : G.induce Sᶜ ≃g G.induce Sᶜ, IsOpposition _ f ∧ ∀ x : ↥Sᶜ, α x = (f x : V)

/-- **Opposition matchings.** Let $K$ be a graph. A subgraph $M$ of $K$ is an opposition matching
of $K$ if it is a perfect matching of $K$ and for any two distinct edges $ab$ and $cd$ of $M$,
$ac \in E(K) \iff bd \in E(K)$ and $ad \in E(K) \iff bc \in E(K)$.

Since both matching edges are present, this says that $K$ induces on $\{a, b, c, d\}$ either
$K_4$, a $4$-cycle, or just the two matching edges.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 2 (opposition matchings). -/
def IsOppositionMatching (K : SimpleGraph V) (M : K.Subgraph) : Prop :=
  M.IsPerfectMatching ∧ ∀ a b c d, M.Adj a b → M.Adj c d → s(a, b) ≠ s(c, d) →
    (K.Adj a c ↔ K.Adj b d) ∧ (K.Adj a d ↔ K.Adj b c)

/-- **Graph product given by a Boolean formula.** Let $G$ and $H$ be graphs with vertex sets $V$
and $W$, and let $\varphi$ be a Boolean function of four Boolean arguments. The product
$G \varphi H$ is the graph on $V \times W$ in which two distinct vertices $(g_1, h_1)$ and
$(g_2, h_2)$ are adjacent exactly when
$\varphi(g_1 g_2 \in E(G), h_1 h_2 \in E(H), g_1 = g_2, h_1 = h_2)$ is true.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 2 (graph products `GφH`). -/
def formulaProduct [DecidableEq V] [DecidableEq W] (φ : Bool → Bool → Bool → Bool → Bool)
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    SimpleGraph (V × W) :=
  SimpleGraph.fromRel fun x y => φ (G.Adj x.1 y.1) (H.Adj x.2 y.2) (x.1 = y.1) (x.2 = y.2)

/-- **Strong product of graphs.** For simple graphs $G$ on $V$ and $H$ on $W$, the strong
product $G \boxtimes H$ is the simple graph on $V \times W$ in which $(g_1, h_1)$ and
$(g_2, h_2)$ are adjacent if and only if $g_1 = g_2$ and $h_1 h_2$ is an edge of $H$, or
$g_1 g_2$ is an edge of $G$ and $h_1 = h_2$, or $g_1 g_2$ is an edge of $G$ and $h_1 h_2$ is
an edge of $H$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 2 (table of
products). -/
abbrev strongProd [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : SimpleGraph (V × W) :=
  formulaProduct (fun eG eH qG qH => (qG && eH) || (eG && qH) || (eG && eH)) G H

/-- **Firework of a graph.** For a graph $G$, vertices $u$ and $v$ of $G$ and a natural number $n$,
the $n$-firework of $G$ at $(u, v)$ is the graph obtained from $G$ by adding $2n$ new vertices,
$n$ of which are adjacent only to $u$ and the other $n$ adjacent only to $v$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 3 (the `n`-firework). -/
def firework (G : SimpleGraph V) (u v : V) (n : ℕ) : SimpleGraph (V ⊕ (Fin n × Bool)) :=
  SimpleGraph.fromRel fun x y => match x, y with
    | Sum.inl a, Sum.inl b => G.Adj a b
    | Sum.inl a, Sum.inr (_, false) => a = u
    | Sum.inl a, Sum.inr (_, true) => a = v
    | _, _ => False

/-- **Strong grid.** For $k \in \mathbb{N}$ and natural numbers $n_0, \dots, n_{k-1}$, the
$k$-dimensional strong grid $P_{n_0} \boxtimes \cdots \boxtimes P_{n_{k-1}}$ is the simple
graph whose vertices are the tuples $(x_0, \dots, x_{k-1})$ of integers with $0 \le x_i < n_i$
for each $i$, in which two vertices $x$ and $y$ are adjacent if and only if $x \ne y$ and
$|x_i - y_i| \le 1$ for every $i$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Corollary 3 (strong
grids). -/
def strongGrid {k : ℕ} (n : Fin k → ℕ) : SimpleGraph ((i : Fin k) → Fin (n i)) :=
  SimpleGraph.fromRel fun x y => ∀ i, (x i : ℕ) ≤ y i + 1 ∧ (y i : ℕ) ≤ x i + 1

instance {k : ℕ} (n : Fin k → ℕ) : DecidableRel (strongGrid n).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ _))

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

/-- **The second player wins Snort on opposable graphs.** If a finite simple graph $G$ is
opposable, then the second player wins Snort on $G$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Lemma 1 (Kakihara,
Proposition 3.6). -/
public theorem_wanted snortSecondPlayerWins_of_isOpposable [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : IsOpposable G) : SnortSecondPlayerWins G

/-- **Oppositions and opposition matchings.** A graph $G$ is opposable if and only if its
complement $\overline{G}$ has an opposition matching.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 1. -/
public theorem_wanted isOpposable_iff_exists_oppositionMatching (G : SimpleGraph V) :
    IsOpposable G ↔ ∃ M : Gᶜ.Subgraph, IsOppositionMatching Gᶜ M

/-- **Gluing oppositions of blocks.** Let $G$ be a graph, let $p$ be a map from its vertices to
an index set, with blocks $B_i = \{v : p(v) = i\}$, and let $f$ be a map from the vertices of $G$
to themselves. Suppose that for every index $i$ there is an opposition of the subgraph of $G$
induced on $B_i$ that agrees with $f$ on $B_i$, and that for all vertices $u, w$ with
$p(u) \neq p(w)$ we have $uw \in E(G) \iff f(u)f(w) \in E(G)$ and
$uf(w) \in E(G) \iff f(u)w \in E(G)$. Then $G$ is opposable.

Since $uf(u)$ and $wf(w)$ are non-edges, the second condition says that the four vertices
$u, f(u), w, f(w)$ induce $C_4$, $2K_2$ or $4K_1$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 2. -/
public theorem_wanted isOpposable_of_blocks {ι : Type*} (G : SimpleGraph V) (p : V → ι)
    (f : V → V)
    (hf : ∀ i, ∃ φ : G.induce {v | p v = i} ≃g G.induce {v | p v = i},
      IsOpposition _ φ ∧ ∀ x, (φ x : V) = f x)
    (hpair : ∀ u w, p u ≠ p w →
      (G.Adj u w ↔ G.Adj (f u) (f w)) ∧ (G.Adj u (f w) ↔ G.Adj (f u) w)) :
    IsOpposable G

/-- **Formula products with an opposable first factor.** Let $G$ and $H$ be graphs, let
$\varphi$ be a Boolean function of four truth values, and let $G \varphi H$ be the formula
product, in which distinct pairs $(g_1, h_1)$ and $(g_2, h_2)$ are adjacent when $\varphi$ is
true at the atoms $g_1g_2 \in E(G)$, $h_1h_2 \in E(H)$, $g_1 = g_2$, $h_1 = h_2$. Suppose that
for all distinct non-adjacent vertices $g_1, g_2$ of $G$ and every vertex $h$ of $H$, $\varphi$
is false at the atoms $g_1g_2 \in E(G)$, $hh \in E(H)$, $g_1 = g_2$, $h = h$ (whose values are
false, false, false, true). If $G$ is opposable, then $G \varphi H$ is opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 3. -/
public theorem_wanted isOpposable_formulaProduct [DecidableEq V] [DecidableEq W]
    (φ : Bool → Bool → Bool → Bool → Bool) (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hφ : ∀ g₁ g₂ : V, ∀ h : W, g₁ ≠ g₂ → ¬ G.Adj g₁ g₂ →
      φ (G.Adj g₁ g₂) (H.Adj h h) (g₁ = g₂) (h = h) = false)
    (hG : IsOpposable G) : IsOpposable (formulaProduct φ G H)

/-- **Standard products with an opposable first factor.** If $G$ is an opposable graph, then for
every graph $H$ the Cartesian product $G \mathbin{\square} H$, the strong product $G \boxtimes H$,
and the tensor, lexicographic, co-normal and homomorphic products of $G$ with $H$ are opposable.
Here distinct pairs $(g_1, h_1)$ and $(g_2, h_2)$ are adjacent in the tensor product when
$g_1g_2 \in E(G)$ and $h_1h_2 \in E(H)$; in the lexicographic product when $g_1g_2 \in E(G)$,
or $g_1 = g_2$ and $h_1h_2 \in E(H)$; in the co-normal product when $g_1g_2 \in E(G)$ or
$h_1h_2 \in E(H)$; and in the homomorphic product when $g_1 = g_2$, or $g_1g_2 \in E(G)$ and
$h_1h_2 \notin E(H)$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Corollary 1. -/
public theorem_wanted isOpposable_products [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : IsOpposable G) :
    IsOpposable (G □ H) ∧ IsOpposable (strongProd G H) ∧
      IsOpposable (formulaProduct (fun eG eH _ _ => eG && eH) G H) ∧
      IsOpposable (formulaProduct (fun eG eH qG _ => eG || (qG && eH)) G H) ∧
      IsOpposable (formulaProduct (fun eG eH _ _ => eG || eH) G H) ∧
      IsOpposable (formulaProduct (fun eG eH qG _ => qG || (eG && !eH)) G H)

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

/-- **Arbitrarily large trees on which the second player wins Snort.** For every natural number
$N$ there is a tree $T$ on $n \ge N$ vertices such that the second player wins Snort on $T$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Corollary 2. -/
public theorem_wanted exists_large_tree_snortSecondPlayerWins (N : ℕ) :
    ∃ n ≥ N, ∃ T : SimpleGraph (Fin n), ∃ _ : DecidableRel T.Adj,
      T.IsTree ∧ SnortSecondPlayerWins T

/-- **Almost opposable graphs are first-player wins in Snort.** For every finite simple graph $G$
that is almost opposable, the first player wins Snort on $G$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Lemma 3. -/
public theorem_wanted snortFirstPlayerWins_of_isAlmostOpposable [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : IsAlmostOpposable G) : SnortFirstPlayerWins G

/-- **Strong products of compatibly almost opposable graphs.** If $G$ and $H$ are compatibly
almost opposable graphs, then their strong product $G \boxtimes H$ is compatibly almost
opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 5. -/
public theorem_wanted isCompatiblyAlmostOpposable_strongProd [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : IsCompatiblyAlmostOpposable G) (hH : IsCompatiblyAlmostOpposable H) :
    IsCompatiblyAlmostOpposable (strongProd G H)

/-- **Strong products with a graph that has a universal vertex.** Let $G$ and $H$ be graphs. If
$G$ is almost opposable and $H$ has a universal vertex, that is, a vertex adjacent to every other
vertex of $H$, then the strong product $G \boxtimes H$ is almost opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 6. -/
public theorem_wanted isAlmostOpposable_strongProd [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : IsAlmostOpposable G) (hH : ∃ v, ∀ w, w ≠ v → H.Adj v w) :
    IsAlmostOpposable (strongProd G H)

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

/-- **Almost opposability of strong grids.** Let $k \ge 1$ and $n_1, \dots, n_k \ge 1$. Then the
$k$-dimensional strong grid $P_{n_1} \boxtimes \cdots \boxtimes P_{n_k}$, the strong product of the
paths $P_{n_i}$ on $n_i$ vertices, is almost opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Corollary 3. -/
public theorem_wanted isAlmostOpposable_strongGrid {k : ℕ} (hk : 1 ≤ k) (n : Fin k → ℕ)
    (hn : ∀ i, 1 ≤ n i) : IsAlmostOpposable (strongGrid n)

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
