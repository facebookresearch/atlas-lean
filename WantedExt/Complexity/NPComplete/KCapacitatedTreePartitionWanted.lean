/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# k-CAPACITATED TREE PARTITION is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MINIMUM K-CAPACITATED TREE PARTITION;
C. Imielińska, B. Kalantari and L. Khachiyan, "A greedy heuristic for a minimum-weight forest
problem", Operations Research Letters 14 (1993), 65-71, doi:10.1016/0167-6377(93)90097-Z
(NP-complete for every fixed `k ≥ 4`; not available to us, result as recorded by Goemans and
Williamson);
M. X. Goemans and D. P. Williamson, "A general approximation technique for constrained forest
problems", SIAM Journal on Computing 24 (1995), 296-317, doi:10.1137/S0097539793242618
(lower capacitated tree partitioning).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.BoundedDiameterSpanningTreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KCapacitatedTreePartition

open BoundedDiameterSpanningTree (BoundedDiameterSpanningTreeInstance endpoints)

/-!
# k-CAPACITATED TREE PARTITION is NP-complete

INSTANCE: a graph `G = (V, E)`, a weight function `w : E → ℕ`, a positive integer `k`, and a
positive integer `K`. QUESTION: is there a `k`-capacitated tree partition of `G`, i.e. a
collection of vertex-disjoint edge sets `E₁, …, E_m ⊆ E` covering the vertices, each forming a
tree with at least `k` vertices, of total weight `∑ᵢ ∑_{e ∈ Eᵢ} w(e)` at most `K`?

This is the decision version of MINIMUM K-CAPACITATED TREE PARTITION in the compendium of
Crescenzi and Kann, the lower capacitated tree partitioning problem of Goemans and Williamson
("vertex-disjoint trees ... that cover all vertices", each with at least `k` vertices).

The instance reuses the type of `BoundedDiameterSpanningTreeWanted` (vertex count `n`, edge list
of triples `(u, v, w)`, two numbers, here `k` and `K`). The union `F` of `E₁, …, E_m` is a
sublist of the edge list (a choice of edges, since the list has no repeated edge); the graph
`forest i F` on all of `V` with the edges of `F` is acyclic (a forest), its connected components
are the trees, each component has at least `k` vertices, and the weight is the sum of `w` over
`F`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `k` and `K` are
positive. -/
def WellFormed (i : BoundedDiameterSpanningTreeInstance) : Prop :=
  ((endpoints i).Nodup ∧
    ∀ e ∈ endpoints i, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ endpoints i) ∧
    0 < i.2.2.1 ∧ 0 < i.2.2.2

/-- The simple graph on the vertices `0, ..., n - 1` made from the edges listed in `F`; it is a
spanning subgraph of `G` when `F` is a sublist of the input edges, as feasibility requires. -/
def forest (i : BoundedDiameterSpanningTreeInstance) (F : List (ℕ × ℕ × ℕ)) :
    SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (F.map fun e => (e.1, e.2.1))

/-- Some set `F ⊆ E` of edges forms a spanning forest whose connected components (trees) have at
least `k` vertices each, of total weight at most `K`. -/
def KCapacitatedTreePartitionFeasible (i : BoundedDiameterSpanningTreeInstance) : Prop :=
  ∃ F : List (ℕ × ℕ × ℕ), F.Sublist i.2.1 ∧ (forest i F).IsAcyclic ∧
    (∀ v, i.2.2.1 ≤ Nat.card ((forest i F).connectedComponentMk v).supp) ∧
    (F.map fun e => e.2.2).sum ≤ i.2.2.2

open Classical in
/-- k-CAPACITATED TREE PARTITION as a decision problem over bitstrings. -/
noncomputable def kCapacitatedTreePartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BoundedDiameterSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ KCapacitatedTreePartitionFeasible i)
  | none => false

/-- **k-CAPACITATED TREE PARTITION is NP-complete.** Source: Crescenzi and Kann, MINIMUM
K-CAPACITATED TREE PARTITION; Imielińska, Kalantari and Khachiyan (1993), as recorded by Goemans
and Williamson (1995). -/
public theorem_wanted kCapacitatedTreePartition_npComplete :
    kCapacitatedTreePartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kCapacitatedTreePartitionDec

end MetaMathlibExt.Complexity.NPComplete.KCapacitatedTreePartition
