/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# METRIC DIMENSION for split graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT61] METRIC DIMENSION;
L. Epstein, A. Levin and G. J. Woeginger, "The (weighted) metric dimension of graphs: hard and
easy cases", Algorithmica 72 (2015), 1130-1171, doi:10.1007/s00453-014-9896-2.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MetricDimensionDefs
public import CSLibExt.Complexity.NPComplete.DominatingSetSplitGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MetricDimensionSplitGraphs

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`, a connected
graph, `0 < K ≤ n`), and the graph is a split graph. -/
def WellFormed (i : MetricDimension.MetricDimensionInstance) : Prop :=
  MetricDimension.WellFormed i ∧ DominatingSetSplitGraphs.IsSplitGraph (MetricDimension.Graph i)

open Classical in
/-- METRIC DIMENSION for split graphs as a decision problem over bitstrings. -/
noncomputable def metricDimensionSplitGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MetricDimension.MetricDimensionInstance) x with
  | some i => decide (WellFormed i ∧ MetricDimension.MetricDimensionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MetricDimensionSplitGraphs
