/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM CYCLE BASIS SPANNING TREE is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide" (fourteenth edition), Journal of
Algorithms 6 (1985), 145-159, problem [2] MINIMUM CYCLE BASIS SPANNING TREE;
N. Deo, G. M. Prabhu and M. S. Krishnamoorthy, "Algorithms for generating fundamental cycles in
a graph", ACM Transactions on Mathematical Software 8(1) (1982), 26-42,
doi:10.1145/355984.355988.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ShortestTotalPathLengthSpanningTreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumCycleBasisSpanningTree

open ShortestTotalPathLengthSpanningTree (ShortestTotalPathLengthSpanningTreeInstance Graph
  WellFormed)

/-!
# MINIMUM CYCLE BASIS SPANNING TREE is NP-complete

INSTANCE: a graph `G = (V, E)` and a bound `B > 0`.
QUESTION: is there a spanning tree `T` of `G` that yields a "cycle basis" for `G` of total length
`B` or less? (The cycle basis corresponding to a given spanning tree `T` consists of all those
simple cycles of `G` that contain exactly one non-tree edge.)

This is Johnson's statement in the fourteenth edition of the NP-completeness column, with the
reference Deo, Prabhu and Krishnamoorthy (1982) (a transformation from SHORTEST TOTAL PATH LENGTH
SPANNING TREE), whose abstract states the problem as finding, in a connected graph, "a spanning
tree in G such that the sum of the lengths of the fundamental cycles (with respect to this tree)
is minimum" and shows it NP-complete. A graph without a spanning tree (a disconnected graph) is a
no-instance here.

For a non-tree edge `{u, v}` of `G`, the only simple cycle of `G` containing it and no other
non-tree edge is the edge together with the path from `u` to `v` in `T`, of length
`T.dist u v + 1`; every simple cycle with exactly one non-tree edge arises this way. So the total
length of the cycle basis is `fundamentalCycleLength G T`, the sum of `T.dist u v + 1` over the
edges `{u, v}` of `G` that are not edges of `T` (each edge once, as `u < v`).

The instance (vertex count `n`, edge list, bound `B`), the graph
(`Cslib.Complexity.Karp.edgeGraph` on `Fin n`), `WellFormed` (simple edge list, `0 < B`) and the
notion of a spanning tree for `G` (a Mathlib `SimpleGraph.IsTree` on all of `V` with `T ≤ G`)
are those of `WantedExt.Complexity.NPComplete.ShortestTotalPathLengthSpanningTreeWanted`
([ND3], the source of the transformation).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- The total length of the fundamental cycles of `G` with respect to `T`: the sum of
`T.dist u v + 1` over the edges `{u, v}` of `G` that are not edges of `T` (each once, as
`u < v`). -/
noncomputable def fundamentalCycleLength {n : ℕ} (G T : SimpleGraph (Fin n)) : ℕ :=
  ∑ u : Fin n, ∑ v ∈ Finset.univ.filter (fun v => u < v ∧ G.Adj u v ∧ ¬ T.Adj u v),
    (T.dist u v + 1)

/-- A spanning tree `T ≤ G` whose fundamental cycles have total length at most `B`. -/
def MinimumCycleBasisSpanningTreeFeasible (i : ShortestTotalPathLengthSpanningTreeInstance) :
    Prop :=
  ∃ T : SimpleGraph (Fin i.1), T ≤ Graph i ∧ T.IsTree ∧
    fundamentalCycleLength (Graph i) T ≤ i.2.2

open Classical in
/-- MINIMUM CYCLE BASIS SPANNING TREE as a decision problem over bitstrings. -/
noncomputable def minimumCycleBasisSpanningTreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShortestTotalPathLengthSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ MinimumCycleBasisSpanningTreeFeasible i)
  | none => false

/-- **MINIMUM CYCLE BASIS SPANNING TREE is NP-complete.** Source: Johnson (1985),
NP-completeness column 14, problem [2]; Deo, Prabhu and Krishnamoorthy (1982). -/
public theorem_wanted minimumCycleBasisSpanningTree_npComplete :
    minimumCycleBasisSpanningTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumCycleBasisSpanningTreeDec

end MetaMathlibExt.Complexity.NPComplete.MinimumCycleBasisSpanningTree
