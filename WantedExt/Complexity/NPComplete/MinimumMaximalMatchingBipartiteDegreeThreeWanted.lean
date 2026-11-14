/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM MAXIMAL MATCHING on bipartite graphs of maximum degree 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT10] MINIMUM MAXIMAL
MATCHING (comment: remains NP-complete for bipartite graphs of maximum degree 3);
M. Yannakakis and F. Gavril, "Edge dominating sets in graphs", SIAM Journal on
Applied Mathematics 38 (1980), 364-372, doi:10.1137/0138030.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MinimumMaximalMatchingWanted
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumMaximalMatchingBipartiteDegreeThree

/-!
# MINIMUM MAXIMAL MATCHING on bipartite graphs of maximum degree 3 is NP-complete

INSTANCE: a graph `G = (V, E)` that is bipartite and has maximum degree at most 3, and a
positive integer `K ≤ |E|`. QUESTION: is there a maximal matching `E'` with `|E'| ≤ K`?

This is the restriction of `WantedExt.Complexity.NPComplete.MinimumMaximalMatchingWanted` to
bipartite graphs of maximum degree at most 3. The instance type, the graph, the parent
well-formedness condition and the question are that module's
(`MinimumMaximalMatching.MinimumMaximalMatchingInstance`, `MinimumMaximalMatching.Graph`,
`MinimumMaximalMatching.WellFormed`, `MinimumMaximalMatching.MinimumMaximalMatchingFeasible`);
the restriction is added to `WellFormed`. Bipartiteness is Mathlib's `SimpleGraph.IsBipartite`
(2-colorability), and degrees are Mathlib's `SimpleGraph.degree`.

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
/-- Well-formedness of an instance: it is a well-formed MINIMUM MAXIMAL MATCHING instance
(simple edge list, `0 < K ≤ |E|`), and its graph is bipartite with every vertex of degree at
most 3. -/
def WellFormed (i : MinimumMaximalMatching.MinimumMaximalMatchingInstance) : Prop :=
  MinimumMaximalMatching.WellFormed i ∧ (MinimumMaximalMatching.Graph i).IsBipartite ∧
    ∀ v, (MinimumMaximalMatching.Graph i).degree v ≤ 3

open Classical in
/-- MINIMUM MAXIMAL MATCHING on bipartite graphs of maximum degree 3 as a decision problem over
bitstrings. -/
noncomputable def minimumMaximalMatchingBipartiteDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumMaximalMatching.MinimumMaximalMatchingInstance) x with
  | some i => decide (WellFormed i ∧ MinimumMaximalMatching.MinimumMaximalMatchingFeasible i)
  | none => false

/-- **MINIMUM MAXIMAL MATCHING is NP-complete on bipartite graphs of maximum degree 3.**
Source: Garey and Johnson (1979), [GT10]; Yannakakis and Gavril (1980). -/
public theorem_wanted minimumMaximalMatchingBipartiteDegreeThree_npComplete :
    minimumMaximalMatchingBipartiteDegreeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumMaximalMatchingBipartiteDegreeThreeDec

end MetaMathlibExt.Complexity.NPComplete.MinimumMaximalMatchingBipartiteDegreeThree
