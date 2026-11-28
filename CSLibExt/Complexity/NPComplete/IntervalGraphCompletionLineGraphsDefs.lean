/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERVAL GRAPH COMPLETION for edge graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT35] INTERVAL GRAPH COMPLETION,
p. 198, comment: "Remains NP-complete when G is restricted to be an edge graph" (the entry is
credited there to Garey, Gavril, and Johnson, 1977, unpublished; not available).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.LineGraph
public import CSLibExt.Complexity.NPComplete.IntervalGraphCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntervalGraphCompletionLineGraphs

open MetaMathlibExt.Complexity.NPComplete.IntervalGraphCompletion

/-- Well-formedness of an instance: a well-formed INTERVAL GRAPH COMPLETION instance whose
graph is an edge graph. -/
def WellFormed (i : IntervalGraphCompletionInstance) : Prop :=
  IntervalGraphCompletion.WellFormed i ∧ MetaMathlibExt.SimpleGraph.IsLineGraph (Graph i)

open Classical in
/-- INTERVAL GRAPH COMPLETION for edge graphs as a decision problem over bitstrings. -/
noncomputable def intervalGraphCompletionLineGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntervalGraphCompletionInstance) x with
  | some i => decide (WellFormed i ∧ IntervalGraphCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IntervalGraphCompletionLineGraphs
