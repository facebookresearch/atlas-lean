/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# METRIC DIMENSION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT61] METRIC
DIMENSION (an unpublished result of the authors);
S. Khuller, B. Raghavachari, and A. Rosenfeld, "Landmarks in graphs",
Discrete Applied Mathematics 70 (1996), 217-229,
doi:10.1016/0166-218X(95)00106-2 (a published proof).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MetricDimension

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev MetricDimensionInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MetricDimensionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the graph is
connected, and `0 < K ≤ |V|`. -/
def WellFormed (i : MetricDimensionInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).Connected ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set of at most `K` vertices resolves every pair of distinct vertices: for distinct `u`
and `v` it contains a vertex `w` with `d(u, w) ≠ d(w, v)`. -/
def MetricDimensionFeasible (i : MetricDimensionInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧
    ∀ u v, u ≠ v → ∃ w ∈ S, (Graph i).dist u w ≠ (Graph i).dist w v

open Classical in
/-- METRIC DIMENSION as a decision problem over bitstrings. -/
noncomputable def metricDimensionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MetricDimensionInstance) x with
  | some i => decide (WellFormed i ∧ MetricDimensionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MetricDimension
