/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROUTING TREE CONGESTION is NP-complete

Source:
P. D. Seymour and R. Thomas, "Call routing and the ratcatcher", Combinatorica 14 (1994),
217-241, doi:10.1007/BF01215352 (definitions in Section 1; deciding whether there is a routing
tree of congestion `< k` is NP-hard for general graphs, even if every weight is `1`);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM ROUTING TREE CONGESTION.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Bioinformatics.Phylogenetics.NeighborJoining
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RoutingTreeCongestion

open Cslib.Bioinformatics.Phylogenetics.NeighborJoining (IsBinaryPhylogeneticTree side)

/-!
# ROUTING TREE CONGESTION is NP-complete

INSTANCE: a graph `G = (V, E)`, a weight function `w : E → ℕ`, and an integer `K ≥ 0`.
QUESTION: is there a routing tree `T` for `G` of congestion at most `K`?

Following Seymour and Thomas, a routing tree for `G` is a tree `T` with `V(G) ⊆ V(T)` in which
every vertex of `G` has valency `1` and every other vertex has valency `3`. For an edge `f` of
`T`, the edges of `G` with ends in different components of `T \ f` are the edges routed along
`f`; the congestion of `T` is the maximum, over the edges `f` of `T`, of the total weight of
the edges routed along `f`. Seymour and Thomas ask for congestion `< k` for an integer `k ≥ 0`;
with integer weights this is congestion at most `K = k - 1`, the compendium's form (`k = 0`
asks for congestion `< 0`, which no routing tree has). A graph with fewer than two
vertices has no routing tree, since a finite tree with at least one edge has at least two
leaves.

The tree is a Mathlib `SimpleGraph` on `Fin m` and `V(G) ⊆ V(T)` is an injection
`τ : Fin n → Fin m`; a routing tree is exactly a binary phylogenetic tree with taxa `V(G)`
(`Cslib.Bioinformatics.Phylogenetics.NeighborJoining.IsBinaryPhylogeneticTree`: a tree whose
degree-one vertices are exactly the `τ v` and whose other vertices have degree three). The
vertices of `G` on the `x`-side of the tree edge `xy` are
`Cslib.Bioinformatics.Phylogenetics.NeighborJoining.side T τ x y`, those whose `τ v` is still
joined to `x` in `T.deleteEdges {s(x, y)}`; an edge of `G` is routed along `xy` when exactly one
of its ends is on that side.

The vertex set is given explicitly as the list `[0, 1, ..., n - 1]`, so an instance's encoding
has length at least `|V|`. With `n` given only in binary, an edgeless graph on many vertices
would be a yes-instance of `O(log |V|)` bits whose natural certificate (a routing tree with
`2|V| - 2` vertices) is exponentially longer, a succinct variant that the cited result does not
cover. The edges are the entries `((u, v), w)` of the weighted edge list, with weight `w`; under
`WellFormed` there are no self-loops and no duplicate edges in either orientation, so the
entries are exactly `E`. Weights use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the vertex list (well-formed when it is `[0, 1, ..., n - 1]`), the weighted
edge list (entries `((u, v), w)`), and the bound `K`. -/
abbrev RoutingTreeCongestionInstance := List ℕ × List ((ℕ × ℕ) × ℕ) × ℕ

/-- Well-formedness of an instance: the vertex list is `[0, 1, ..., n - 1]` with `n` its
length, and the edges describe a simple graph on `0, …, n - 1` (no duplicate edges in either
orientation, no self-loops, endpoints in range). -/
def WellFormed (i : RoutingTreeCongestionInstance) : Prop :=
  i.1 = List.range i.1.length ∧
    ((i.2.1.map Prod.fst).Nodup ∧ ∀ e ∈ i.2.1.map Prod.fst, e.1 < i.1.length ∧
      e.2 < i.1.length ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1.map Prod.fst)

/-- The vertex `v` of `G` (if `v < n`) lies on the `x`-side of the tree edge `xy`. -/
def OnSide {n m : ℕ} (T : SimpleGraph (Fin m)) (τ : Fin n → Fin m) (x y : Fin m) (v : ℕ) :
    Prop :=
  ∃ h : v < n, (⟨v, h⟩ : Fin n) ∈ side T τ x y

open Classical in
/-- The total weight of the edges of `G` routed along the tree edge `xy`: those with exactly one
end on the side of `x`. -/
noncomputable def routedWeight {n m : ℕ} (T : SimpleGraph (Fin m)) (τ : Fin n → Fin m)
    (x y : Fin m) (es : List ((ℕ × ℕ) × ℕ)) : ℕ :=
  ((es.filter fun e => decide (¬(OnSide T τ x y e.1.1 ↔ OnSide T τ x y e.1.2))).map
    Prod.snd).sum

open Classical in
/-- `(T, τ)` is a routing tree for the graph on `0, …, n - 1` with weighted edges `es`, of
congestion at most `K`: a binary phylogenetic tree with taxa `τ v` (a tree, with `τ` a bijection
from the graph vertices onto its degree-one vertices, every other vertex of degree three), with
at most `K` weight routed along every edge of `T`. -/
def IsRoutingTreeOfCongestion (n : ℕ) (es : List ((ℕ × ℕ) × ℕ)) (K : ℕ) {m : ℕ}
    (T : SimpleGraph (Fin m)) (τ : Fin n → Fin m) : Prop :=
  IsBinaryPhylogeneticTree T τ ∧ ∀ x y, T.Adj x y → routedWeight T τ x y es ≤ K

/-- Some routing tree for `G` has congestion at most `K`. -/
def RoutingTreeCongestionFeasible (i : RoutingTreeCongestionInstance) : Prop :=
  ∃ (m : ℕ) (T : SimpleGraph (Fin m)) (τ : Fin i.1.length → Fin m),
    IsRoutingTreeOfCongestion i.1.length i.2.1 i.2.2 T τ

open Classical in
/-- ROUTING TREE CONGESTION as a decision problem over bitstrings. -/
noncomputable def routingTreeCongestionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RoutingTreeCongestionInstance) x with
  | some i => decide (WellFormed i ∧ RoutingTreeCongestionFeasible i)
  | none => false

/-- **ROUTING TREE CONGESTION is NP-complete.** Source: Seymour and Thomas (1994); Crescenzi and
Kann, MINIMUM ROUTING TREE CONGESTION. -/
public theorem_wanted routingTreeCongestion_npComplete :
    routingTreeCongestionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L routingTreeCongestionDec

end MetaMathlibExt.Complexity.NPComplete.RoutingTreeCongestion
