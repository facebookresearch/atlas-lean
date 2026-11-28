/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MIN-MAX MULTICENTER with unit weights and lengths on planar graphs of maximum degree 3:
definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND50] MIN-MAX MULTICENTER, p. 220
(comment: "Remains NP-complete if `w(v) = 1` for all `v ∈ V` and `l(e) = 1` for all `e ∈ E`"),
and problem [GT2] DOMINATING SET, p. 190 (comment: "Remains NP-complete for planar graphs with
maximum vertex degree 3");
O. Kariv and S. L. Hakimi, "An algorithmic approach to network location problems. I: The
p-centers", SIAM Journal on Applied Mathematics 37 (1979), 513-538, doi:10.1137/0137040;
A. Kolen, "Complexity of location problems on networks", Report BW 107/79, Mathematisch Centrum,
Amsterdam (1979), Theorem 1.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Set.Card
public import CSLibExt.Complexity.NPComplete.MinMaxMulticenterDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinMaxMulticenterUnitPlanarDegreeThree

open MetaMathlibExt.Complexity.NPComplete.MinMaxMulticenter
  (MinMaxMulticenterInstance Graph MinMaxMulticenterFeasible)

/-- Well-formedness of an instance: a well-formed MIN-MAX MULTICENTER instance with all weights
`1` and all edge lengths `1`, whose graph is planar with maximum degree at most 3. -/
def WellFormed (i : MinMaxMulticenterInstance) : Prop :=
  MinMaxMulticenter.WellFormed i ∧ (∀ w ∈ i.2.2.1, w = 1) ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    (Graph i).IsPlanar ∧ ∀ v : Fin i.1, ((Graph i).neighborSet v).ncard ≤ 3

open Classical in
/-- MIN-MAX MULTICENTER with unit weights and lengths on planar graphs of maximum degree 3, as a
decision problem over bitstrings. -/
noncomputable def minMaxMulticenterUnitPlanarDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinMaxMulticenterInstance) x with
  | some i => decide (WellFormed i ∧ MinMaxMulticenterFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinMaxMulticenterUnitPlanarDegreeThree
