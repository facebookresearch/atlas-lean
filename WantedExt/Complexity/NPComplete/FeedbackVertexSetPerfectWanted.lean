/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on perfect graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET, the problem
restricted here;
A. Brandstädt, S. Brito, S. Klein, L. T. Nogueira and F. Protti, "Cycle transversals in perfect
graphs and cographs", Theoretical Computer Science 469 (2013), 15-23,
doi:10.1016/j.tcs.2012.10.030.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Combinatorics.SimpleGraph.PerfectGraph
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.FeedbackVertexSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetPerfect

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet

/-!
# FEEDBACK VERTEX SET on perfect graphs is NP-complete

INSTANCE: a perfect graph `G = (V, E)` (finite, simple, undirected) and a nonnegative integer
`K`.
QUESTION: is there a set `V' ⊆ V` with `|V'| ≤ K` such that `G - V'` is a forest, that is,
`V'` meets every cycle of `G`?

A graph is perfect when every induced subgraph `H` has chromatic number equal to its clique
number, `χ(H) = ω(H)`; this is MathlibExt's
`MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted.IsPerfect` (every induced subgraph
`G.induce s`, `s : Set V`, has `chromaticNumber = cliqueNum`). The instance, its
well-formedness and the question are those of the undirected FEEDBACK VERTEX SET
(`WantedExt.Complexity.NPComplete.FeedbackVertexSetWanted`: a simple graph on `Fin n` given by
an edge list and the bound `K`; the question asks for at most `K` vertices whose removal leaves
an acyclic induced subgraph, Mathlib's `SimpleGraph.IsAcyclic`). The restriction adds that the
graph is perfect (ISGCI class `gc_56`).

Brandstädt, Brito, Klein, Nogueira and Protti prove that finding a minimum cycle transversal (a
feedback vertex set) of a perfect graph is NP-hard, even for bipartite graphs with maximum degree
four; the graphs their reduction outputs are bipartite, hence perfect, so it is a reduction to
this problem. Membership in NP: the certificate is `V'` (acyclicity of `G - V'` is checked in
polynomial time), and whether `G` is perfect is decidable in polynomial time: perfect graphs are
the Berge graphs (no odd hole or odd antihole) by the strong perfect graph theorem of Chudnovsky,
Robertson, Seymour and Thomas (Annals of Mathematics 164 (2006), 51-229,
doi:10.4007/annals.2006.164.51), and Berge graphs are recognized in polynomial time by
Chudnovsky, Cornuéjols, Liu, Seymour and Vušković ("Recognizing Berge graphs", Combinatorica 25
(2005), 143-186, doi:10.1007/s00493-005-0012-8).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed FEEDBACK VERTEX SET instance whose graph is
perfect. -/
def WellFormed (i : FeedbackVertexSetInstance) : Prop :=
  FeedbackVertexSet.WellFormed i ∧
    MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted.IsPerfect (Graph i)

open Classical in
/-- FEEDBACK VERTEX SET on perfect graphs as a decision problem over bitstrings. -/
noncomputable def feedbackVertexSetPerfectDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSetFeasible i)
  | none => false

/-- **FEEDBACK VERTEX SET on perfect graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT7]; Brandstädt, Brito, Klein, Nogueira and Protti (2013). -/
public theorem_wanted feedbackVertexSetPerfect_npComplete :
    feedbackVertexSetPerfectDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feedbackVertexSetPerfectDec

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetPerfect
