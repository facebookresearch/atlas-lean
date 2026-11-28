/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET for chordal graphs: definitions

Source:
K. S. Booth and J. H. Johnson, "Dominating sets in chordal graphs", SIAM Journal on Computing
11(1) (1982), 191-199, doi:10.1137/0211015;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetChordalGraphs

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`), the graph is
chordal (no induced cycle of length at least `4`), and `0 < K ≤ n`. -/
def WellFormed (i : DominatingSet.DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧
    (∀ k, 4 ≤ k → ¬ (SimpleGraph.cycleGraph k).IsIndContained (DominatingSet.Graph i)) ∧
      0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- DOMINATING SET for chordal graphs as a decision problem over bitstrings. -/
noncomputable def dominatingSetChordalGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSet.DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSet.DominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DominatingSetChordalGraphs
