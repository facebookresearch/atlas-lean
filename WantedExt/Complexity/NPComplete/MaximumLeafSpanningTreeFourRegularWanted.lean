/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM LEAF SPANNING TREE on 4-regular graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND2] MAXIMUM LEAF SPANNING TREE,
comment on p. 206 ("Remains NP-complete if G is regular of degree 4"; reference
[Garey and Johnson, ——], unpublished results);
A. Reich, "Complexity of the maximum leaf spanning tree problem on planar and regular graphs",
Theoretical Computer Science 626 (2016), 134-143, doi:10.1016/j.tcs.2016.02.011, Section 1
(records the 4-regular case with its attribution to Garey and Johnson).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MaximumLeafSpanningTreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumLeafSpanningTreeFourRegular

open MetaMathlibExt.Complexity.NPComplete.MaximumLeafSpanningTree
  (MaximumLeafSpanningTreeInstance MaximumLeafSpanningTreeFeasible)

/-!
# MAXIMUM LEAF SPANNING TREE on 4-regular graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is regular of degree 4, and a positive integer `K ≤ |V|`.
QUESTION: is there a spanning tree for `G` in which `K` or more vertices have degree 1?

The instance and the question are those of MAXIMUM LEAF SPANNING TREE
(`WantedExt.Complexity.NPComplete.MaximumLeafSpanningTreeWanted`: a nonempty simple graph on
`Fin n` given by an edge list, and the bound `K`; the question asks for `n - 1` distinct edges of
`G` forming a connected spanning subgraph, hence a spanning tree, together with at least `K`
vertices each incident with exactly one of its edges). The restriction adds that the graph is
regular of degree 4 (Mathlib's `SimpleGraph.IsRegularOfDegree 4`: every vertex has degree 4)
and, as in the source, `0 < K ≤ |V|`.

Garey and Johnson state the 4-regular case in the entry whose reference is their own
unpublished results (a transformation from DOMINATING SET); Reich (2016) records it with that
attribution. Membership in NP is inherited: the certificate is the tree and its leaves, and
4-regularity is checked in polynomial time.

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
/-- Well-formedness of an instance: a well-formed MAXIMUM LEAF SPANNING TREE instance whose
graph is regular of degree 4, with `0 < K ≤ |V|`. -/
def WellFormed (i : MaximumLeafSpanningTreeInstance) : Prop :=
  MaximumLeafSpanningTree.WellFormed i ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsRegularOfDegree 4 ∧
      0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- MAXIMUM LEAF SPANNING TREE on 4-regular graphs as a decision problem over bitstrings. -/
noncomputable def maximumLeafSpanningTreeFourRegularDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumLeafSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ MaximumLeafSpanningTreeFeasible i)
  | none => false

/-- **MAXIMUM LEAF SPANNING TREE on 4-regular graphs is NP-complete.** Source: Garey and
Johnson (1979), [ND2]; Reich (2016). -/
public theorem_wanted maximumLeafSpanningTreeFourRegular_npComplete :
    maximumLeafSpanningTreeFourRegularDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumLeafSpanningTreeFourRegularDec

end MetaMathlibExt.Complexity.NPComplete.MaximumLeafSpanningTreeFourRegular
