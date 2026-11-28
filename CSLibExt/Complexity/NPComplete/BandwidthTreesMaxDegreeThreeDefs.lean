/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BANDWIDTH for trees of maximum degree 3: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT40] BANDWIDTH (comment: remains
NP-complete for trees with no vertex degree exceeding 3);
M. R. Garey, R. L. Graham, D. S. Johnson and D. E. Knuth, "Complexity results for bandwidth
minimization", SIAM Journal on Applied Mathematics 34 (1978), 477-495, doi:10.1137/0134037.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Complexity.NPComplete.BandwidthDefs
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BandwidthTreesMaxDegreeThree

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : Bandwidth.BandwidthInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

open Classical in
/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`), the graph is a
tree with every vertex of degree at most `3`, and `0 < K ≤ n`. -/
def WellFormed (i : Bandwidth.BandwidthInstance) : Prop :=
  Bandwidth.WellFormed i ∧ (Graph i).IsTree ∧ (∀ v, (Graph i).degree v ≤ 3) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- BANDWIDTH for trees of maximum degree 3 as a decision problem over bitstrings. -/
noncomputable def bandwidthTreesMaxDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := Bandwidth.BandwidthInstance) x with
  | some i => decide (WellFormed i ∧ Bandwidth.BandwidthFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BandwidthTreesMaxDegreeThree
