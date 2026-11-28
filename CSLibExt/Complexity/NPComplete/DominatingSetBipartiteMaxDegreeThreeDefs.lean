/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on bipartite graphs of maximum degree 3: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 190, problem [GT2] DOMINATING SET,
comment: "Remains NP-complete for planar graphs with maximum vertex degree 3" [Garey and
Johnson, unpublished];
I. E. Zverovich and V. E. Zverovich, "An induced subgraph characterization of domination
perfect graphs", Journal of Graph Theory 20 (1995), 375-395, doi:10.1002/jgt.3190200313;
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_941`
(bipartite ∩ maximum degree 3, https://www.graphclasses.org/classes/gc_941.html), problem
Domination: NP-complete, from the subclass bipartite ∩ girth >= 9 ∩ maximum degree 3 ∩ planar
(Zverovich and Zverovich 1995).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetBipartiteMaxDegreeThree

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

open Classical in
/-- Well-formedness of an instance: a well-formed DOMINATING SET instance with `0 < K ≤ |V|`
whose graph is bipartite and of maximum degree at most `3`. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧ (Graph i).IsBipartite ∧
    ∀ v, (Graph i).degree v ≤ 3

open Classical in
/-- DOMINATING SET on bipartite graphs of maximum degree 3 as a decision problem over
bitstrings. -/
noncomputable def dominatingSetBipartiteMaxDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DominatingSetBipartiteMaxDegreeThree
