/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# k-CAPACITATED TREE PARTITION: definitions

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

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BoundedDiameterSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KCapacitatedTreePartition

open BoundedDiameterSpanningTree (BoundedDiameterSpanningTreeInstance endpoints)

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

end MetaMathlibExt.Complexity.NPComplete.KCapacitatedTreePartition
