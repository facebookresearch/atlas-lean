/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT DOMINATING SET on planar bipartite subcubic graphs of girth at least 9: definitions

Source:
I. E. Zverovich and V. E. Zverovich, "An induced subgraph characterization of domination
perfect graphs", Journal of Graph Theory 20(3) (1995), 375-395, doi:10.1002/jgt.3190200313;
ISGCI, Information System on Graph Classes and their Inclusions, class bipartite ∩ girth >= 9 ∩
maximum degree 3 ∩ planar (gc_1226, https://www.graphclasses.org/classes/gc_1226.html), problem
Independent dominating set;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), p. 190, problem [GT2] DOMINATING SET, comment: "Also
NP-complete if V' is required to be both a dominating set and an independent set."
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DominatingSetPlanarBipartiteSubcubicGirthNineDefs
public import CSLibExt.Complexity.NPComplete.IndependentDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSetPlanarBipartiteSubcubicGirthNine

/-- Well-formedness of an instance: the instance class of
`DominatingSetPlanarBipartiteSubcubicGirthNine` (a simple edge list on `Fin n`, `0 < K ≤ n`, and
a planar bipartite graph of maximum degree at most `3` and girth at least `9`). -/
def WellFormed (i : IndependentDominatingSet.IndependentDominatingSetInstance) : Prop :=
  DominatingSetPlanarBipartiteSubcubicGirthNine.WellFormed i

open Classical in
/-- INDEPENDENT DOMINATING SET on planar bipartite subcubic graphs of girth at least 9 as a
decision problem over bitstrings. -/
noncomputable def independentDominatingSetPlanarBipartiteSubcubicGirthNineDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IndependentDominatingSet.IndependentDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ IndependentDominatingSet.IndependentDominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSetPlanarBipartiteSubcubicGirthNine
