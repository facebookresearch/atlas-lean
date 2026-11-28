/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM MAXIMAL MATCHING on planar graphs of maximum degree 3: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT10] MINIMUM MAXIMAL
MATCHING (comment: remains NP-complete for planar graphs of maximum degree 3);
M. Yannakakis and F. Gavril, "Edge dominating sets in graphs", SIAM Journal on
Applied Mathematics 38 (1980), 364-372, doi:10.1137/0138030.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumMaximalMatchingDefs
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumMaximalMatchingPlanarDegreeThree

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

end MetaMathlibExt.Complexity.NPComplete.MinimumMaximalMatchingPlanarDegreeThree
