/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MIN-SUM MULTICENTER with unit weights and lengths on planar graphs of maximum degree 3: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND51] MIN-SUM MULTICENTER (p. 220),
comment "Remains NP-complete if w(v) = 1 for all v ∈ V and l(e) = 1 for all e ∈ E";
O. Kariv and S. L. Hakimi, "An algorithmic approach to network location problems. II: The
p-medians", SIAM Journal on Applied Mathematics 37 (1979), 539-560, doi:10.1137/0137041
(NP-hard "even when the network has a simple structure (e.g., planar graph of maximum vertex
degree 3)").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import CSLibExt.Complexity.NPComplete.MinSumMulticenterDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinSumMulticenterUnitPlanarMaxDegreeThree

open MetaMathlibExt.Complexity.NPComplete.MinSumMulticenter

open Classical in
/-- Well-formedness of an instance: a well-formed MIN-SUM MULTICENTER instance in which every
vertex weight and every edge length is `1`, whose graph is planar with every vertex degree at
most `3`. -/
def WellFormed (i : MinSumMulticenterInstance) : Prop :=
  MinSumMulticenter.WellFormed i ∧ (∀ w ∈ i.2.2.1, w = 1) ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    (Graph i).IsPlanar ∧ ∀ v, (Graph i).degree v ≤ 3

open Classical in
/-- MIN-SUM MULTICENTER with unit weights and lengths on planar graphs of maximum degree 3 as
a decision problem over bitstrings. -/
noncomputable def minSumMulticenterUnitPlanarMaxDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinSumMulticenterInstance) x with
  | some i => decide (WellFormed i ∧ MinSumMulticenterFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinSumMulticenterUnitPlanarMaxDegreeThree
