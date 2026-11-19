/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# K-CLUSTER (DENSEST k-SUBGRAPH) on chordal graphs is NP-complete

Source:
D. G. Corneil and Y. Perl, "Clustering and domination in perfect graphs", Discrete Applied
Mathematics 9(1) (1984), 27-39, doi:10.1016/0166-218X(84)90088-X (abstract: "it is shown that
the k-cluster problem is NP-complete for both bipartite and chordal graphs").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import WantedExt.Complexity.NPComplete.DensestKSubgraphWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DensestKSubgraphChordal

open MetaMathlibExt.Complexity.NPComplete.DensestKSubgraph
  (DensestKSubgraphInstance DensestKSubgraphFeasible)

/-!
# K-CLUSTER (DENSEST k-SUBGRAPH) on chordal graphs is NP-complete

INSTANCE: a chordal graph `G = (V, E)`, that is, a graph in which every cycle of length at least
`4` has a chord, and positive integers `k` and `J`.
QUESTION: is there a set `V' ⊆ V` with `|V'| = k` such that the subgraph `G[V']` induced by `V'`
has at least `J` edges?

Corneil and Perl define a `k`-cluster as an induced subgraph on `k` vertices with the maximum
number of edges; the decision version asks whether `k` vertices induce at least `J` edges. This
is DENSEST k-SUBGRAPH (`DensestKSubgraphWanted`) restricted to chordal graphs. The instance type
and the question are the parent's (`DensestKSubgraph.DensestKSubgraphInstance`: vertex count
`n`, edge list, `k`, `J`; `DensestKSubgraph.DensestKSubgraphFeasible`: a set of exactly `k`
vertices below `n` and a sublist of at least `J` listed edges with both endpoints in the set,
which under the parent's simple edge list counts edges of `G[V']`). `WellFormed` is the parent's
plus the restriction and the source's positivity of `k` and `J`. Chordality is stated, as in
`PathwidthChordalGraphsWanted` and `DominatingSetChordalGraphsWanted`, on the instance's graph
`Cslib.Complexity.Karp.edgeGraph`: no cycle graph `Cₘ` with `m ≥ 4` is an induced subgraph
(Mathlib's `SimpleGraph.cycleGraph` and `SimpleGraph.IsIndContained`; a cycle has a chord exactly
when its vertices do not induce a cycle graph).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the parent's (a simple edge list on `0, ..., n - 1`), the
graph is chordal (no induced cycle of length at least `4`), and `0 < k`, `0 < J`. -/
def WellFormed (i : DensestKSubgraphInstance) : Prop :=
  DensestKSubgraph.WellFormed i ∧
    (∀ m, 4 ≤ m →
      ¬ (SimpleGraph.cycleGraph m).IsIndContained (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1)) ∧
      0 < i.2.2.1 ∧ 0 < i.2.2.2

open Classical in
/-- K-CLUSTER on chordal graphs as a decision problem over bitstrings. -/
noncomputable def densestKSubgraphChordalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DensestKSubgraphInstance) x with
  | some i => decide (WellFormed i ∧ DensestKSubgraphFeasible i)
  | none => false

/-- **K-CLUSTER (DENSEST k-SUBGRAPH) on chordal graphs is NP-complete.** Source: Corneil and
Perl (1984). -/
public theorem_wanted densestKSubgraphChordal_npComplete :
    densestKSubgraphChordalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L densestKSubgraphChordalDec

end MetaMathlibExt.Complexity.NPComplete.DensestKSubgraphChordal
