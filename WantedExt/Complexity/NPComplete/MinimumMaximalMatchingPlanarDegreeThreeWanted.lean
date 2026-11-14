/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM MAXIMAL MATCHING on planar graphs of maximum degree 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT10] MINIMUM MAXIMAL
MATCHING (comment: remains NP-complete for planar graphs of maximum degree 3);
M. Yannakakis and F. Gavril, "Edge dominating sets in graphs", SIAM Journal on
Applied Mathematics 38 (1980), 364-372, doi:10.1137/0138030.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MinimumMaximalMatchingWanted
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumMaximalMatchingPlanarDegreeThree

/-!
# MINIMUM MAXIMAL MATCHING on planar graphs of maximum degree 3 is NP-complete

INSTANCE: a graph `G = (V, E)` that is planar and has maximum degree at most 3, and a positive
integer `K ≤ |E|`. QUESTION: is there a maximal matching `E'` with `|E'| ≤ K`?

This is the restriction of `WantedExt.Complexity.NPComplete.MinimumMaximalMatchingWanted` to
planar graphs of maximum degree at most 3. The instance type, the graph, the parent
well-formedness condition and the question are that module's
(`MinimumMaximalMatching.MinimumMaximalMatchingInstance`, `MinimumMaximalMatching.Graph`,
`MinimumMaximalMatching.WellFormed`, `MinimumMaximalMatching.MinimumMaximalMatchingFeasible`);
the restriction is added to `WellFormed`. Planarity is `SimpleGraph.IsPlanar` from
`MathlibExt.Combinatorics.SimpleGraph.Planarity` (a crossing-free straight-line drawing), which
for finite simple graphs is planarity by Fáry's theorem; degrees are Mathlib's
`SimpleGraph.degree`.

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
(simple edge list, `0 < K ≤ |E|`), and its graph is planar with every vertex of degree at
most 3. -/
def WellFormed (i : MinimumMaximalMatching.MinimumMaximalMatchingInstance) : Prop :=
  MinimumMaximalMatching.WellFormed i ∧ (MinimumMaximalMatching.Graph i).IsPlanar ∧
    ∀ v, (MinimumMaximalMatching.Graph i).degree v ≤ 3

open Classical in
/-- MINIMUM MAXIMAL MATCHING on planar graphs of maximum degree 3 as a decision problem over
bitstrings. -/
noncomputable def minimumMaximalMatchingPlanarDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumMaximalMatching.MinimumMaximalMatchingInstance) x with
  | some i => decide (WellFormed i ∧ MinimumMaximalMatching.MinimumMaximalMatchingFeasible i)
  | none => false

/-- **MINIMUM MAXIMAL MATCHING is NP-complete on planar graphs of maximum degree 3.** Source:
Garey and Johnson (1979), [GT10]; Yannakakis and Gavril (1980). -/
public theorem_wanted minimumMaximalMatchingPlanarDegreeThree_npComplete :
    minimumMaximalMatchingPlanarDegreeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumMaximalMatchingPlanarDegreeThreeDec

end MetaMathlibExt.Complexity.NPComplete.MinimumMaximalMatchingPlanarDegreeThree
