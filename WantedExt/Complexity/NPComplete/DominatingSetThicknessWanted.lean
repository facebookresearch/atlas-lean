/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on graphs of thickness at most k (fixed k ≥ 1) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET, comment
("Remains NP-complete for planar graphs with maximum vertex degree 3 [...]");
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 5(1)
(1984), 147-160, doi:10.1016/0196-6774(84)90045-2, Section 3 (the result was proved for 3-regular
planar graphs, also by Kikuno and Kakuda; the "regular of degree 4" class that [GT2] also lists
was a transcription error);
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3)
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Section 3 (thickness-k graphs) and Table 1
(thickness-k graphs, DOMINATING SET: NP-complete, citing Garey and Johnson).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DominatingSetWanted
public import WantedExt.Complexity.NPComplete.GraphThicknessWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetThickness

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-!
# DOMINATING SET on graphs of thickness at most k is NP-complete

Fix an integer `k ≥ 1`.
INSTANCE: a graph `G = (V, E)` of thickness at most `k` and a positive integer `K ≤ |V|`.
QUESTION: is there a dominating set `V' ⊆ V` with `|V'| ≤ K`, that is, every vertex not in `V'`
has a neighbor in `V'`?

Johnson (1985) defines the thickness-`k` graphs as the "graphs `G = (V, E)` where `E` can be
partitioned into sets `E₁` through `E_k` such that `Gᵢ = (V, Eᵢ)` is planar, `1 ≤ i ≤ k`", for a
fixed `k`, and lists DOMINATING SET as NP-complete for them, citing Garey and Johnson, who record
that it remains NP-complete for planar graphs of maximum degree 3; Johnson (1984) confirms the
result for 3-regular planar graphs and withdraws the planar 4-regular class also listed in [GT2]
as a transcription error. A planar graph has thickness
at most `1 ≤ k` (all edges in `E₁`), so those instances are instances of this problem for every
fixed `k ≥ 1`. Membership in NP: the certificate is `V'` together with the partition
`E₁, …, E_k`; domination is checked directly and each `Gᵢ` by a polynomial-time planarity test.

The instance, the graph and the question are those of
`WantedExt.Complexity.NPComplete.DominatingSetWanted` ([GT2]: a simple graph on `Fin n` given by
an edge list, and the bound `K`). The restriction adds `0 < K ≤ |V|` as in [GT2], and that the
graph has thickness at most `k`: the question of GRAPH THICKNESS
(`GraphThickness.GraphThicknessFeasible` from
`WantedExt.Complexity.NPComplete.GraphThicknessWanted`) holds for the same vertex count and
edge list with the bound `k` (`withThickness`): the edges are split into `k` classes, each
spanning a planar subgraph on all vertices, with the shared straight-line planarity predicate
`SimpleGraph.IsPlanar` (by Fáry's theorem, planarity for finite simple graphs).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The GRAPH THICKNESS instance with the same vertex count and edge list and the bound `k`. -/
def withThickness (k : ℕ) (i : DominatingSetInstance) : GraphThickness.GraphThicknessInstance :=
  (i.1, i.2.1, k)

/-- Well-formedness of an instance for the fixed thickness bound `k`: a well-formed DOMINATING
SET instance (a simple edge list on `Fin n`) whose graph has thickness at most `k`, with
`0 < K ≤ |V| = n`. -/
def WellFormed (k : ℕ) (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ GraphThickness.GraphThicknessFeasible (withThickness k i) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- DOMINATING SET on graphs of thickness at most `k`, for the fixed `k`, as a decision problem
over bitstrings. -/
noncomputable def dominatingSetThicknessDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed k i ∧ DominatingSetFeasible i)
  | none => false

/-- **DOMINATING SET on graphs of thickness at most `k` is NP-complete for every fixed
`k ≥ 1`.** Source: Garey and Johnson (1979), [GT2], comment; Johnson (1984), Section 3;
Johnson (1985), Table 1. -/
public theorem_wanted dominatingSetThickness_npComplete (k : ℕ) (_hk : 1 ≤ k) :
    dominatingSetThicknessDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (dominatingSetThicknessDec k)

end MetaMathlibExt.Complexity.NPComplete.DominatingSetThickness
