/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on bipartite graphs: definitions

Source:
A. A. Bertossi, "Dominating sets for split and bipartite graphs", Information Processing
Letters 19(1) (1984), 37-40, doi:10.1016/0020-0190(84)90126-1;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetBipartite

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-- Well-formedness of an instance: a well-formed DOMINATING SET instance whose graph is
bipartite, with `0 < K`. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ (Graph i).IsBipartite ∧ 0 < i.2.2

open Classical in
/-- DOMINATING SET on bipartite graphs as a decision problem over bitstrings. -/
noncomputable def dominatingSetBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DominatingSetBipartite
