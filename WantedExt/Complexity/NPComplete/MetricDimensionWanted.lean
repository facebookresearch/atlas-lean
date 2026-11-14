/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# METRIC DIMENSION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT61] METRIC
DIMENSION (an unpublished result of the authors);
S. Khuller, B. Raghavachari, and A. Rosenfeld, "Landmarks in graphs",
Discrete Applied Mathematics 70 (1996), 217-229,
doi:10.1016/0166-218X(95)00106-2 (a published proof).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MetricDimension

/-!
# METRIC DIMENSION is NP-complete

INSTANCE: a connected graph `G = (V, E)` and a positive integer `K ≤ |V|`. QUESTION: is there a
subset `V' ⊆ V` with `|V'| ≤ K` such that for each pair `u, v` of distinct vertices there is a
vertex `w ∈ V'` with `d(u, w) ≠ d(w, v)`? Such a `V'` is a resolving set (a set of landmarks).

The distance `d` is Mathlib's `SimpleGraph.dist`, the length of a shortest walk; it is the
graph distance because `WellFormed` requires `G` to be connected (Mathlib's `dist` is `0` for
unreachable pairs, and the metric dimension is defined for connected graphs).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **METRIC DIMENSION is NP-complete.** Source: Garey and Johnson (1979), [GT61]; Khuller,
Raghavachari, and Rosenfeld (1996). -/
public theorem_wanted metricDimension_npComplete :
    metricDimensionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L metricDimensionDec

end MetaMathlibExt.Complexity.NPComplete.MetricDimension
