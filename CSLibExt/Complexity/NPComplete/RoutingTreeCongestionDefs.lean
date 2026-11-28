/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROUTING TREE CONGESTION: definitions

Source:
P. D. Seymour and R. Thomas, "Call routing and the ratcatcher", Combinatorica 14 (1994),
217-241, doi:10.1007/BF01215352 (definitions in Section 1; deciding whether there is a routing
tree of congestion `< k` is NP-hard for general graphs, even if every weight is `1`);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MINIMUM ROUTING TREE CONGESTION.
-/
module

public import CSLibExt.Bioinformatics.Phylogenetics.NeighborJoining
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RoutingTreeCongestion

open Cslib.Bioinformatics.Phylogenetics.NeighborJoining (IsBinaryPhylogeneticTree side)

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
congestion at most `K`: a binary phylogenetic tree with taxa `τ v` (a tree whose degree-one
vertices are exactly the `τ v`, every other vertex of degree three), with at most `K` weight
routed along every edge of `T`. -/
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

end MetaMathlibExt.Complexity.NPComplete.RoutingTreeCongestion
