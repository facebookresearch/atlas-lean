/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET in segment intersection graphs: definitions

Source:
J. Kratochvíl and J. Nešetřil, "INDEPENDENT SET and CLIQUE problems in intersection-defined
classes of graphs", Commentationes Mathematicae Universitatis Carolinae 31(1) (1990), 85-93,
http://dml.cz/dmlcz/106821 (Theorem 1);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SegmentIntersectionCliqueDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetSegmentIntersection

open SegmentIntersectionClique (SegmentIntersectionCliqueInstance Graph)

/-- The intersection graph of the segments has an independent set of size `K` or more. -/
def IndependentSetSegmentIntersectionFeasible (i : SegmentIntersectionCliqueInstance) : Prop :=
  ∃ S : Finset (Fin i.1.length), i.2 ≤ S.card ∧ (Graph i).IsIndepSet (S : Set (Fin i.1.length))

open Classical in
/-- INDEPENDENT SET in segment intersection graphs as a decision problem over bitstrings. -/
noncomputable def independentSetSegmentIntersectionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SegmentIntersectionCliqueInstance) x with
  | some i => decide (SegmentIntersectionClique.WellFormed i ∧
      IndependentSetSegmentIntersectionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IndependentSetSegmentIntersection
