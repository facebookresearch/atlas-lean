/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# METRIC DIMENSION on planar graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT61] METRIC DIMENSION;
J. Díaz, O. Pottonen, M. Serna and E. J. van Leeuwen, "Complexity of metric dimension on planar
graphs", Journal of Computer and System Sciences 83(1) (2017), 132-158,
doi:10.1016/j.jcss.2016.06.006 (arXiv:1107.2256), Theorem 3.6.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MetricDimensionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MetricDimensionPlanar

open MetaMathlibExt.Complexity.NPComplete

/-!
# METRIC DIMENSION on planar graphs is NP-complete

INSTANCE: a connected planar graph `G = (V, E)` and a positive integer `K ≤ |V|`. QUESTION: is
there a subset `V' ⊆ V` with `|V'| ≤ K` such that for each pair `u, v` of distinct vertices
there is a vertex `w ∈ V'` with `d(u, w) ≠ d(w, v)`? Díaz, Pottonen, Serna and van Leeuwen
(2017), Theorem 3.6: "Planar Metric Dimension is NP-complete, even on graphs of maximum degree
6" (their graphs are finite, undirected and connected).

This is METRIC DIMENSION (`MetaMathlibExt.Complexity.NPComplete.MetricDimension`, Garey and
Johnson's [GT61]) restricted to planar graphs. The instance type, the graph, the
well-formedness conditions (simple edge list, connected, `0 < K ≤ |V|`) and the question are
that module's; this module adds only planarity to `WellFormed`. Planarity is the shared
MathlibExt predicate `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing; by Fáry's
theorem this is planarity for finite simple graphs).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **METRIC DIMENSION on planar graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT61]; Díaz, Pottonen, Serna and van Leeuwen (2017), Theorem 3.6. -/
public theorem_wanted metricDimensionPlanar_npComplete :
    metricDimensionPlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L metricDimensionPlanarDec

end MetaMathlibExt.Complexity.NPComplete.MetricDimensionPlanar
