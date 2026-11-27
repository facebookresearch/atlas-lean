/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on bipartite graphs is NP-complete

Source:
A. A. Bertossi, "Dominating sets for split and bipartite graphs", Information Processing
Letters 19(1) (1984), 37-40, doi:10.1016/0020-0190(84)90126-1;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetBipartite

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-!
# DOMINATING SET on bipartite graphs is NP-complete

INSTANCE: a bipartite graph `G = (V, E)` and a positive integer `K`.
QUESTION: is there a dominating set `V' ⊆ V` with `|V'| ≤ K`, that is, every vertex not in `V'`
has a neighbor in `V'`?

The instance, its well-formedness and the question are those of
`CSLibExt.Complexity.NPComplete.DominatingSetDefs` ([GT2]: a simple graph on `Fin n` given by
an edge list, and the bound `K`). The restriction adds that the graph is bipartite, as Mathlib's
`SimpleGraph.IsBipartite` (`Colorable 2`: the vertices split into two sets with every edge
between them). As in the source, `K` is positive.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed DOMINATING SET instance whose graph is
bipartite, with `0 < K`. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ (Graph i).IsBipartite ∧ 0 < i.2.2

open Classical in
/-- DOMINATING SET on bipartite graphs as a decision problem over bitstrings. -/
noncomputable def dominatingSetBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

/-- **DOMINATING SET on bipartite graphs is NP-complete.** Source: Bertossi (1984). -/
public theorem_wanted dominatingSetBipartite_npComplete :
    dominatingSetBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetBipartite
