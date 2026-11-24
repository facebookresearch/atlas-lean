/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERVAL GRAPH COMPLETION for edge graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT35] INTERVAL GRAPH COMPLETION,
p. 198, comment: "Remains NP-complete when G is restricted to be an edge graph" (the entry is
credited there to Garey, Gavril, and Johnson, 1977, unpublished; not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.LineGraph
public import WantedExt.Complexity.NPComplete.IntervalGraphCompletionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntervalGraphCompletionLineGraphs

open MetaMathlibExt.Complexity.NPComplete.IntervalGraphCompletion

/-!
# INTERVAL GRAPH COMPLETION for edge graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is an edge graph (line graph), and an integer `K`.
QUESTION: is there a superset `E'` containing `E` such that `|E' - E| ≤ K` and the graph
`G' = (V, E')` is an interval graph?

This is the restriction of [GT35] INTERVAL GRAPH COMPLETION
(`WantedExt.Complexity.NPComplete.IntervalGraphCompletionWanted`) recorded in Garey and
Johnson's comment. The instance, its well-formedness and the question are those of the parent:
a simple graph on `Fin n` given by an edge list, the bound `K`, and an interval supergraph `H`
of `G` on the same vertices with at most `K` edges not in `G`. As in the parent, `K` is
positive; Garey and Johnson state `K` as a non-negative integer, and the case `K = 0` (is `G`
an interval graph?) is solvable in polynomial time. The restriction adds that `G` is an edge
graph, `MetaMathlibExt.SimpleGraph.IsLineGraph`: isomorphic to Mathlib's `SimpleGraph.lineGraph`
`L(R)` of a graph `R` on some `Fin k` (the vertices of `L(R)` are the edges of `R`, two being
adjacent when they share an endpoint). Line graphs are recognized, and a root graph found, in
linear time (P. G. H. Lehot, "An optimal algorithm to detect a line graph and output its root
graph", Journal of the ACM 21 (1974), 569-575, doi:10.1145/321850.321853), so the restriction
does not affect membership in NP.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed INTERVAL GRAPH COMPLETION instance whose
graph is an edge graph. -/
def WellFormed (i : IntervalGraphCompletionInstance) : Prop :=
  IntervalGraphCompletion.WellFormed i ∧ MetaMathlibExt.SimpleGraph.IsLineGraph (Graph i)

open Classical in
/-- INTERVAL GRAPH COMPLETION for edge graphs as a decision problem over bitstrings. -/
noncomputable def intervalGraphCompletionLineGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntervalGraphCompletionInstance) x with
  | some i => decide (WellFormed i ∧ IntervalGraphCompletionFeasible i)
  | none => false

/-- **INTERVAL GRAPH COMPLETION for edge graphs is NP-complete.** Source: Garey and Johnson
(1979), [GT35], comment. -/
public theorem_wanted intervalGraphCompletionLineGraphs_npComplete :
    intervalGraphCompletionLineGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L intervalGraphCompletionLineGraphsDec

end MetaMathlibExt.Complexity.NPComplete.IntervalGraphCompletionLineGraphs
