/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on 2-DIR graphs: definitions

Source:
J. Kratochvíl and J. Nešetřil, "INDEPENDENT SET and CLIQUE problems in intersection-defined
classes of graphs", Commentationes Mathematicae Universitatis Carolinae 31(1) (1990), 85-93,
http://dml.cz/dmlcz/106821 (Theorem 1: "INDEPENDENT SET is polynomially solvable in 1-DIR and
PURE-2-DIR, but it is NP-complete when restricted to 2-DIR and PURE-3-DIR");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET (the parent problem);
ISGCI (https://www.graphclasses.org/classes/gc_864.html), class "2-DIR", problem "Independent
set": NP-complete.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TriangleFreeIndependentSetDefs
public import CSLibExt.Complexity.NPComplete.TwoDirRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetTwoDir

open TriangleFreeIndependentSet (TriangleFreeIndependentSetInstance Graph
  TriangleFreeIndependentSetFeasible)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`
(`TwoDirRecognition.WellFormed`), the graph is a 2-DIR graph, and `0 < K ≤ n`. -/
def WellFormed (i : TriangleFreeIndependentSetInstance) : Prop :=
  TwoDirRecognition.WellFormed (i.1, i.2.1) ∧ TwoDirRecognition.IsTwoDir (Graph i) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- INDEPENDENT SET on 2-DIR graphs as a decision problem over bitstrings. -/
noncomputable def independentSetTwoDirDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TriangleFreeIndependentSetInstance) x with
  | some i => decide (WellFormed i ∧ TriangleFreeIndependentSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IndependentSetTwoDir
