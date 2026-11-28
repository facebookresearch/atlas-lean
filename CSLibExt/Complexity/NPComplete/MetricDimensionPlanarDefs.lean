/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# METRIC DIMENSION on planar graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT61] METRIC DIMENSION;
J. Díaz, O. Pottonen, M. Serna and E. J. van Leeuwen, "Complexity of metric dimension on planar
graphs", Journal of Computer and System Sciences 83(1) (2017), 132-158,
doi:10.1016/j.jcss.2016.06.006 (arXiv:1107.2256), Theorem 3.6.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MetricDimensionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MetricDimensionPlanar

open MetaMathlibExt.Complexity.NPComplete

/-- Well-formedness of an instance: the instance is a well-formed METRIC DIMENSION instance (a
simple edge list whose graph is connected, and `0 < K ≤ |V|`), and its graph is planar. -/
def WellFormed (i : MetricDimension.MetricDimensionInstance) : Prop :=
  MetricDimension.WellFormed i ∧ (MetricDimension.Graph i).IsPlanar

open Classical in
/-- METRIC DIMENSION on planar graphs as a decision problem over bitstrings. -/
noncomputable def metricDimensionPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MetricDimension.MetricDimensionInstance) x with
  | some i => decide (WellFormed i ∧ MetricDimension.MetricDimensionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MetricDimensionPlanar
