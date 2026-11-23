/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# METRIC TRAVELING SALESPERSON is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND22] TRAVELING SALESMAN, comment:
"Remains NP-complete even if d(cᵢ, cⱼ) ∈ {1, 2} for all cᵢ, cⱼ ∈ C" (transformation from
HAMILTONIAN CIRCUIT);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), MINIMUM METRIC TRAVELING SALESPERSON PROBLEM.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.TspWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MetricTravelingSalesperson

open Tsp (TspInstance TspFeasible)

/-!
# METRIC TRAVELING SALESPERSON is NP-complete

INSTANCE: a set `C` of `m` cities, a distance `d(cᵢ, cⱼ) ∈ ℤ⁺` for each pair of distinct cities,
satisfying the triangle inequality, and a positive integer `B`.
QUESTION: is there a tour of `C`, i.e. a permutation `π` of the cities, of length
`∑ᵢ d(c_π(i), c_π(i+1)) + d(c_π(m), c_π(1)) ≤ B`?

This is TRAVELING SALESPERSON (`TspWanted`, Garey and Johnson [ND22]) restricted to distances
that satisfy the triangle inequality `d(a, c) ≤ d(a, b) + d(b, c)`, the decision version of the
compendium's MINIMUM METRIC TRAVELING SALESPERSON PROBLEM. Garey and Johnson record that TSP
remains NP-complete when every distance is `1` or `2`; such distances satisfy the triangle
inequality (`2 ≤ 1 + 1`), so the hard instances (from HAMILTONIAN CIRCUIT, NP-complete by Karp,
"Reducibility among combinatorial problems" (1972): distance `1` on edges, `2` on non-edges,
`B = m`) are metric. The instance (city count, symmetric distance matrix with zero
diagonal, bound), the parent's well-formedness and the question are those of `TspWanted`; the
restriction adds to `WellFormed` Garey and Johnson's positive distances between distinct cities
(`d(cᵢ, cⱼ) ∈ ℤ⁺`), the triangle inequality, and their positive bound `B` (the zero diagonal is
the parent's encoding of the distance from a city to itself).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed TRAVELING SALESPERSON instance (a symmetric
`m × m` distance matrix with zero diagonal, `0 < m`) whose distances between distinct cities are
positive and satisfy the triangle inequality `d(a, c) ≤ d(a, b) + d(b, c)`, and `0 < B`. -/
def WellFormed (i : TspInstance) : Prop :=
  Tsp.WellFormed i ∧
    (∀ a < i.1, ∀ b < i.1, a ≠ b → 0 < (i.2.1.getD a []).getD b 0) ∧
    (∀ a < i.1, ∀ b < i.1, ∀ c < i.1,
      (i.2.1.getD a []).getD c 0 ≤ (i.2.1.getD a []).getD b 0 + (i.2.1.getD b []).getD c 0) ∧
    0 < i.2.2

open Classical in
/-- METRIC TRAVELING SALESPERSON as a decision problem over bitstrings. -/
noncomputable def metricTravelingSalespersonDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TspInstance) x with
  | some i => decide (WellFormed i ∧ TspFeasible i)
  | none => false

/-- **METRIC TRAVELING SALESPERSON is NP-complete.** Source: Garey and Johnson (1979), [ND22]
(distances `1` and `2`). -/
public theorem_wanted metricTravelingSalesperson_npComplete :
    metricTravelingSalespersonDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L metricTravelingSalespersonDec

end MetaMathlibExt.Complexity.NPComplete.MetricTravelingSalesperson
