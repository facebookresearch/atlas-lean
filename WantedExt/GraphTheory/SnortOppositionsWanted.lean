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

/-- Snort with fuel `k`: whether the player to move, who owns the coloured set
`mine` while the opponent owns `theirs`, has a winning strategy. A legal move
colours a vertex outside `mine ∪ theirs` with no neighbour in `theirs`; with
no fuel left the mover is declared to lose.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 1 (rules of
Snort). -/
def snortMoverWins [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ℕ → Finset V → Finset V → Bool
  | 0, _, _ => false
  | k + 1, mine, theirs =>
      decide (∃ v : V, v ∉ mine ∧ v ∉ theirs ∧ (∀ w ∈ theirs, ¬ G.Adj v w) ∧
        snortMoverWins G k theirs (insert v mine) = false)

/-- The first player wins Snort on the (untinted) graph `G`.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 1. -/
def SnortFirstPlayerWins [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  snortMoverWins G (Fintype.card V) ∅ ∅ = true

/-- The second player wins Snort on the (untinted) graph `G`.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 1. -/
def SnortSecondPlayerWins [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  snortMoverWins G (Fintype.card V) ∅ ∅ = false

/-- `(u, v)` is a response pair: the first player colouring `u` and the second
answering `v` is legal and leaves a position that the first player, now to
move, loses.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 3 (response
pair). -/
def IsSnortResponsePair [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : Prop :=
  u ≠ v ∧ ¬ G.Adj u v ∧ snortMoverWins G (Fintype.card V - 2) {u} {v} = false

/-- An opposition: an involutive automorphism moving every vertex outside its
closed neighbourhood.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 1 (after
Kakihara). -/
def IsOpposition (G : SimpleGraph V) (f : G ≃g G) : Prop :=
  ∀ v, f (f v) = v ∧ f v ≠ v ∧ ¬ G.Adj v (f v)

/-- `G` is opposable: it has an opposition.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 1. -/
def IsOpposable (G : SimpleGraph V) : Prop :=
  ∃ f : G ≃g G, IsOpposition G f

/-- `G` is almost opposable: `G - S` is opposable for some admissible `S`
(`u ∈ S ⊆ N[u]`).

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 4 (almost opposable graphs). -/
def IsAlmostOpposable (G : SimpleGraph V) : Prop :=
  ∃ u : V, ∃ S : Set V, u ∈ S ∧ S ⊆ insert u (G.neighborSet u) ∧ IsOpposable (G.induce Sᶜ)

/-- `G` is compatibly almost opposable: for some admissible `S`, `G - S` has an
opposition `f` agreeing on `V ∖ S` with an involutive automorphism `α` of `G`.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 4 (compatibly almost opposable
graphs). -/
def IsCompatiblyAlmostOpposable (G : SimpleGraph V) : Prop :=
  ∃ u : V, ∃ S : Set V, u ∈ S ∧ S ⊆ insert u (G.neighborSet u) ∧
    ∃ α : G ≃g G, (∀ v, α (α v) = v) ∧
      ∃ f : G.induce Sᶜ ≃g G.induce Sᶜ, IsOpposition _ f ∧ ∀ x : ↥Sᶜ, α x = (f x : V)

/-- An opposition matching of `K`: a perfect matching such that for any two
distinct matching edges `ab`, `cd` the graph `K` induces on `{a, b, c, d}` is
`K₄`, `C₄`, or just the two matching edges; since both matching edges are
present, this says exactly that `ac ∈ E ↔ bd ∈ E` and `ad ∈ E ↔ bc ∈ E`.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 2 (opposition matchings). -/
def IsOppositionMatching (K : SimpleGraph V) (M : K.Subgraph) : Prop :=
  M.IsPerfectMatching ∧ ∀ a b c d, M.Adj a b → M.Adj c d → s(a, b) ≠ s(c, d) →
    (K.Adj a c ↔ K.Adj b d) ∧ (K.Adj a d ↔ K.Adj b c)

/-- The graph product `G φ H` on `V × W` given by a Boolean function `φ` of the
atoms `g₁g₂ ∈ E(G)`, `h₁h₂ ∈ E(H)`, `g₁ = g₂`, `h₁ = h₂` (symmetric in the two
endpoints, so `fromRel` only removes loops).

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 2 (graph products `GφH`). -/
def formulaProduct [DecidableEq V] [DecidableEq W] (φ : Bool → Bool → Bool → Bool → Bool)
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    SimpleGraph (V × W) :=
  SimpleGraph.fromRel fun x y => φ (G.Adj x.1 y.1) (H.Adj x.2 y.2) (x.1 = y.1) (x.2 = y.2)

/-- The strong product `G ⊠ H`: the formula product for
`(g₁ = g₂ ∧ h₁h₂ ∈ E) ∨ (g₁g₂ ∈ E ∧ h₁ = h₂) ∨ (g₁g₂ ∈ E ∧ h₁h₂ ∈ E)`.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 2 (table of
products). -/
abbrev strongProd [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : SimpleGraph (V × W) :=
  formulaProduct (fun eG eH qG qH => (qG && eH) || (eG && qH) || (eG && eH)) G H

/-- The `n`-firework of `G` at `(u, v)`: `n` new leaves attached to `u`
(`inr (i, false)`) and `n` to `v` (`inr (i, true)`).

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 3 (the `n`-firework). -/
def firework (G : SimpleGraph V) (u v : V) (n : ℕ) : SimpleGraph (V ⊕ (Fin n × Bool)) :=
  SimpleGraph.fromRel fun x y => match x, y with
    | Sum.inl a, Sum.inl b => G.Adj a b
    | Sum.inl a, Sum.inr (_, false) => a = u
    | Sum.inl a, Sum.inr (_, true) => a = v
    | _, _ => False

/-- The `k`-dimensional strong grid `⊠ᵢ P_{nᵢ}`: distinct points whose
coordinates all differ by at most one.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Corollary 3 (strong
grids). -/
def strongGrid {k : ℕ} (n : Fin k → ℕ) : SimpleGraph ((i : Fin k) → Fin (n i)) :=
  SimpleGraph.fromRel fun x y => ∀ i, (x i : ℕ) ≤ y i + 1 ∧ (y i : ℕ) ≤ x i + 1

instance {k : ℕ} (n : Fin k → ℕ) : DecidableRel (strongGrid n).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ _))

/-- The `k`-dimensional Cartesian grid `□ᵢ P_{nᵢ}`: points differing in exactly
one coordinate, by one.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Corollary 4 (Cartesian
grids). -/
def cartesianGrid {k : ℕ} (n : Fin k → ℕ) : SimpleGraph ((i : Fin k) → Fin (n i)) :=
  SimpleGraph.fromRel fun x y => ∃ i, (x i : ℕ) + 1 = y i ∧ ∀ j, j ≠ i → x j = y j

instance {k : ℕ} (n : Fin k → ℕ) : DecidableRel (cartesianGrid n).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ _))

/-- The King's grid on `Fin n × Fin m`.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 5. -/
def kingGraph (n m : ℕ) : SimpleGraph (Fin n × Fin m) :=
  SimpleGraph.fromRel fun x y => |(x.1 : ℤ) - y.1| ≤ 1 ∧ |(x.2 : ℤ) - y.2| ≤ 1

instance (n m : ℕ) : DecidableRel (kingGraph n m).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ _))

/-- The Knight's grid on `Fin n × Fin m`.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 5 (proof of
Theorem 9). -/
def knightGraph (n m : ℕ) : SimpleGraph (Fin n × Fin m) :=
  SimpleGraph.fromRel fun x y =>
    (|(x.1 : ℤ) - y.1| = 1 ∧ |(x.2 : ℤ) - y.2| = 2) ∨
      (|(x.1 : ℤ) - y.1| = 2 ∧ |(x.2 : ℤ) - y.2| = 1)

instance (n m : ℕ) : DecidableRel (knightGraph n m).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ _))

/-- The Bishop's grid on `Fin n × Fin m`: distinct cells on a common diagonal.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 5 (proof of
Theorem 10). -/
def bishopGraph (n m : ℕ) : SimpleGraph (Fin n × Fin m) :=
  SimpleGraph.fromRel fun x y => |(x.1 : ℤ) - y.1| = |(x.2 : ℤ) - y.2|

instance (n m : ℕ) : DecidableRel (bishopGraph n m).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ _))

/-- The Queen's grid on `Fin n × Fin m`: distinct cells sharing a row, a column,
or a diagonal.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 5. -/
def queenGraph (n m : ℕ) : SimpleGraph (Fin n × Fin m) :=
  SimpleGraph.fromRel fun x y =>
    x.1 = y.1 ∨ x.2 = y.2 ∨ |(x.1 : ℤ) - y.1| = |(x.2 : ℤ) - y.2|

instance (n m : ℕ) : DecidableRel (queenGraph n m).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ _))

instance (n m : ℕ) : DecidableRel (SimpleGraph.rookGraph n m).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ _))

/-- The first player wins Snort on `K₂`, and the second player wins on two
isolated vertices.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 1; characteristic
check of `snortMoverWins`. -/
theorem snort_two_vertices :
    SnortFirstPlayerWins (⊤ : SimpleGraph (Fin 2)) ∧
      SnortSecondPlayerWins (⊥ : SimpleGraph (Fin 2)) := by
  unfold SnortFirstPlayerWins SnortSecondPlayerWins; decide

/-- The first player wins the Peaceable Queens game on a `2 × 2` board, and the
second player wins the Peaceable Rooks game there.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 5; characteristic
check of `queenGraph` and `SimpleGraph.rookGraph`. -/
theorem snort_two_by_two :
    SnortFirstPlayerWins (queenGraph 2 2) ∧ SnortSecondPlayerWins (SimpleGraph.rookGraph 2 2) := by
  unfold SnortFirstPlayerWins SnortSecondPlayerWins; decide

/-- The second player wins Snort on every opposable graph.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Lemma 1 (Kakihara,
Proposition 3.6). -/
public theorem_wanted snortSecondPlayerWins_of_isOpposable [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : IsOpposable G) : SnortSecondPlayerWins G

/-- `G` has an opposition iff its complement has an opposition matching.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 1. -/
public theorem_wanted isOpposable_iff_exists_oppositionMatching (G : SimpleGraph V) :
    IsOpposable G ↔ ∃ M : Gᶜ.Subgraph, IsOppositionMatching Gᶜ M

/-- If the blocks `{v | p v = i}` induce opposable graphs with oppositions given
by `f`, and for paired vertices `{u, f u}` and `{w, f w}` in different blocks the
four vertices induce `C₄`, `2K₂` or `4K₁` (as the two nonedges `u f(u)`,
`w f(w)` force: `uw ∈ E ↔ f(u)f(w) ∈ E` and `u f(w) ∈ E ↔ f(u) w ∈ E`), then `G`
is opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 2. -/
public theorem_wanted isOpposable_of_blocks {ι : Type*} (G : SimpleGraph V) (p : V → ι)
    (f : V → V)
    (hf : ∀ i, ∃ φ : G.induce {v | p v = i} ≃g G.induce {v | p v = i},
      IsOpposition _ φ ∧ ∀ x, (φ x : V) = f x)
    (hpair : ∀ u w, p u ≠ p w →
      (G.Adj u w ↔ G.Adj (f u) (f w)) ∧ (G.Adj u (f w) ↔ G.Adj (f u) w)) :
    IsOpposable G

/-- If `((h₁ = h₂) ∧ ¬(g₁g₂ ∈ E(G))) ⇒ ¬φ` for distinct `g₁, g₂` and `G` is
opposable, then `G φ H` is opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 3. -/
public theorem_wanted isOpposable_formulaProduct [DecidableEq V] [DecidableEq W]
    (φ : Bool → Bool → Bool → Bool → Bool) (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hφ : ∀ g₁ g₂ : V, ∀ h : W, g₁ ≠ g₂ → ¬ G.Adj g₁ g₂ →
      φ (G.Adj g₁ g₂) (H.Adj h h) (g₁ = g₂) (h = h) = false)
    (hG : IsOpposable G) : IsOpposable (formulaProduct φ G H)

/-- If `G` is opposable then so are its Cartesian, strong, tensor,
lexicographic, co-normal and homomorphic products with any `H`.

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

/-- If the second player wins Snort on `G` with a response pair `(u, v)` at
distance at least `3`, then the second player wins on the `n`-firework for every
`n ≥ |V(G)|`.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 4. -/
public theorem_wanted snortSecondPlayerWins_firework [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (hG : SnortSecondPlayerWins G)
    (huv : IsSnortResponsePair G u v) (hdist : 3 ≤ G.edist u v) (n : ℕ)
    (hn : Fintype.card V ≤ n) [DecidableRel (firework G u v n).Adj] :
    SnortSecondPlayerWins (firework G u v n)

/-- There are infinitely many trees on which the second player wins Snort.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Corollary 2. -/
public theorem_wanted exists_large_tree_snortSecondPlayerWins (N : ℕ) :
    ∃ n ≥ N, ∃ T : SimpleGraph (Fin n), ∃ _ : DecidableRel T.Adj,
      T.IsTree ∧ SnortSecondPlayerWins T

/-- The first player wins Snort on every almost opposable graph.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Lemma 3. -/
public theorem_wanted snortFirstPlayerWins_of_isAlmostOpposable [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : IsAlmostOpposable G) : SnortFirstPlayerWins G

/-- The strong product of compatibly almost opposable graphs is compatibly almost
opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 5. -/
public theorem_wanted isCompatiblyAlmostOpposable_strongProd [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : IsCompatiblyAlmostOpposable G) (hH : IsCompatiblyAlmostOpposable H) :
    IsCompatiblyAlmostOpposable (strongProd G H)

/-- If `G` is almost opposable and `H` has a universal vertex, then `G ⊠ H` is
almost opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 6. -/
public theorem_wanted isAlmostOpposable_strongProd [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : IsAlmostOpposable G) (hH : ∃ v, ∀ w, w ≠ v → H.Adj v w) :
    IsAlmostOpposable (strongProd G H)

/-- If `G` and `H` are compatibly almost opposable and `G - u` has a compatible
opposition for some `u` (the admissible set `{u}`), then `G □ H` is compatibly
almost opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 7. -/
public theorem_wanted isCompatiblyAlmostOpposable_boxProd (G : SimpleGraph V)
    (H : SimpleGraph W) (hG : IsCompatiblyAlmostOpposable G) (hH : IsCompatiblyAlmostOpposable H)
    (hu : ∃ u : V, ∃ α : G ≃g G, (∀ v, α (α v) = v) ∧
      ∃ f : G.induce ({u}ᶜ : Set V) ≃g G.induce ({u}ᶜ : Set V),
        IsOpposition _ f ∧ ∀ x : ↥({u}ᶜ : Set V), α x = (f x : V)) :
    IsCompatiblyAlmostOpposable (G □ H)

/-- Every strong grid `⊠_{i=1}^k P_{nᵢ}` with `k ≥ 1` and all `nᵢ ≥ 1` is almost
opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Corollary 3. -/
public theorem_wanted isAlmostOpposable_strongGrid {k : ℕ} (hk : 1 ≤ k) (n : Fin k → ℕ)
    (hn : ∀ i, 1 ≤ n i) : IsAlmostOpposable (strongGrid n)

/-- For `k ≥ 1` and all `nᵢ ≥ 1`, the Cartesian grid `□_{i=1}^k P_{nᵢ}` is almost
opposable iff at most one `nᵢ` is even, and otherwise it is opposable.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Corollary 4. -/
public theorem_wanted cartesianGrid_opposability {k : ℕ} (hk : 1 ≤ k) (n : Fin k → ℕ)
    (hn : ∀ i, 1 ≤ n i) :
    (IsAlmostOpposable (cartesianGrid n) ↔ (Finset.univ.filter fun i => Even (n i)).card ≤ 1) ∧
      (1 < (Finset.univ.filter fun i => Even (n i)).card → IsOpposable (cartesianGrid n))

/-- The first player wins the Peaceable Kings game on every `n × m` board.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 8. -/
public theorem_wanted snortFirstPlayerWins_kingGraph (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    SnortFirstPlayerWins (kingGraph n m)

/-- The second player wins the Peaceable Knights game on `n × m` iff `n` or `m`
is even.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 9. -/
public theorem_wanted snortSecondPlayerWins_knightGraph_iff (n m : ℕ) (hn : 1 ≤ n)
    (hm : 1 ≤ m) : SnortSecondPlayerWins (knightGraph n m) ↔ Even n ∨ Even m

/-- The second player wins the Peaceable Bishops game on `n × m` iff `n` or `m`
is even.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 10. -/
public theorem_wanted snortSecondPlayerWins_bishopGraph_iff (n m : ℕ) (hn : 1 ≤ n)
    (hm : 1 ≤ m) : SnortSecondPlayerWins (bishopGraph n m) ↔ Even n ∨ Even m

/-- The second player wins the Peaceable Rooks game on `n × m` iff `n` and `m`
are both even.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 11. -/
public theorem_wanted snortSecondPlayerWins_rookGraph_iff (n m : ℕ) (hn : 1 ≤ n)
    (hm : 1 ≤ m) : SnortSecondPlayerWins (SimpleGraph.rookGraph n m) ↔ Even n ∧ Even m

/-- If `n` or `m` is odd, the first player wins the Peaceable Queens game on
`n × m`.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Theorem 12. -/
public theorem_wanted snortFirstPlayerWins_queenGraph (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h : Odd n ∨ Odd m) : SnortFirstPlayerWins (queenGraph n m)

end

end MetaMathlibExt
