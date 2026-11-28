/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT DOMINATING SET for 2P₃-free graphs: definitions

Source:
I. E. Zverovich, "Satgraphs and independent domination. Part 1", Theoretical Computer Science
352(1-3) (2006), 47-56, doi:10.1016/j.tcs.2005.08.038;
ISGCI, Information System on Graph Classes and their Inclusions, class 2P₃-free (gc_931,
https://www.graphclasses.org/classes/gc_931.html), problem Independent dominating set;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import CSLibExt.Complexity.NPComplete.IndependentDominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSetTwoP3Free

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`), the graph has
no induced `2P₃`, and `0 < K ≤ n`. -/
def WellFormed (i : IndependentDominatingSet.IndependentDominatingSetInstance) : Prop :=
  IndependentDominatingSet.WellFormed i ∧
    ¬ (SimpleGraph.pathGraph 3 ⊕g SimpleGraph.pathGraph 3).IsIndContained
      (IndependentDominatingSet.Graph i) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- INDEPENDENT DOMINATING SET for 2P₃-free graphs as a decision problem over bitstrings. -/
noncomputable def independentDominatingSetTwoP3FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IndependentDominatingSet.IndependentDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ IndependentDominatingSet.IndependentDominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IndependentDominatingSetTwoP3Free
