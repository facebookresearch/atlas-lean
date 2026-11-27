/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT on tripartite graphs is NP-complete

Source:
H. L. Bodlaender and K. Jansen, "On the complexity of the maximum cut problem", Technical Report
RUU-CS-91-39, Department of Computer Science, Utrecht University (1991), abstract (SIMPLE MAX CUT
"is NP-complete when restricted to one of the following classes: chordal graphs, undirected path
graphs, split graphs, tripartite graphs, and graphs that are the complement of a bipartite
graph"); conference version STACS 94, LNCS 775 (1994), 769-780,
doi:10.1007/3-540-57785-8_189; journal version Nordic Journal of Computing 7(1) (2000), 14-31.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaxCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutTripartite

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)

/-!
# SIMPLE MAX CUT on tripartite graphs is NP-complete

INSTANCE: a tripartite graph `G = (V, E)`, that is, one whose vertex set can be partitioned into
three independent sets, and a positive integer `K`.
QUESTION: is there a partition of `V` into two sets with at least `K` edges between them?

This is SIMPLE MAX CUT (MAX CUT with all edge weights one) restricted to tripartite graphs, which
Bodlaender and Jansen prove NP-complete. The instance, the simple-edge-list conditions and the
question are those of MAXIMUM CUT (`MaxCutDefs`, whose question counts edges), reused as in
`SimpleMaxCutUndirectedPathGraphsWanted`; the restriction adds to `WellFormed` that
`Cslib.Complexity.Karp.edgeGraph` is tripartite, Mathlib's `Colorable 3` (a partition into three
independent sets, some possibly empty, is a proper coloring with three colors), and `0 < K`.

Membership in NP: a 3-coloring of the vertices on edges (vertices outside the edge list are
isolated and take any color) and a cut are a polynomial certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
the vertices `0, ..., n - 1`) whose graph is tripartite (3-colorable), and `0 < K`. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  MaxCut.WellFormed i ∧ (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).Colorable 3 ∧ 0 < i.2.2

open Classical in
/-- SIMPLE MAX CUT on tripartite graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutTripartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ MaxCutFeasible i)
  | none => false

/-- **SIMPLE MAX CUT on tripartite graphs is NP-complete.** Source: Bodlaender and Jansen (1991;
STACS 1994; Nordic J. Computing 2000). -/
public theorem_wanted simpleMaxCutTripartite_npComplete :
    simpleMaxCutTripartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L simpleMaxCutTripartiteDec

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutTripartite
