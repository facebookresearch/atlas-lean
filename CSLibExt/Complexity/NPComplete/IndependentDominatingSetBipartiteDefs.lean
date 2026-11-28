/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT DOMINATING SET on bipartite graphs: definitions

Source:
D. G. Corneil and Y. Perl, "Clustering and domination in perfect graphs", Discrete Applied
Mathematics 9(1) (1984), 27-39, doi:10.1016/0166-218X(84)90088-X;
ISGCI, Information System on Graph Classes and their Inclusions, class bipartite (gc_69,
https://www.graphclasses.org/classes/gc_69.html), problem Independent dominating set;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DominatingSetBipartiteDefs
public import CSLibExt.Complexity.NPComplete.IndependentDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSetBipartite

open MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSet

open Classical in
/-- INDEPENDENT DOMINATING SET on bipartite graphs as a decision problem over bitstrings. -/
noncomputable def independentDominatingSetBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IndependentDominatingSetInstance) x with
  | some i => decide (DominatingSetBipartite.WellFormed i ∧ IndependentDominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSetBipartite
