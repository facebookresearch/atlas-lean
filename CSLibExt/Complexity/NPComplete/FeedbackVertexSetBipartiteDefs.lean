/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on bipartite graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET;
A. Brandstädt, S. Brito, S. Klein, L. T. Nogueira and F. Protti, "Cycle transversals in perfect
graphs and cographs", Theoretical Computer Science 469 (2013), 15-23,
doi:10.1016/j.tcs.2012.10.030.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import CSLibExt.Complexity.NPComplete.FeedbackVertexSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetBipartite

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet

/-- Well-formedness of an instance: a well-formed FEEDBACK VERTEX SET instance whose graph is
bipartite. -/
def WellFormed (i : FeedbackVertexSetInstance) : Prop :=
  FeedbackVertexSet.WellFormed i ∧ (Graph i).IsBipartite

open Classical in
/-- FEEDBACK VERTEX SET on bipartite graphs as a decision problem over bitstrings. -/
noncomputable def feedbackVertexSetBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed i ∧ FeedbackVertexSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetBipartite
