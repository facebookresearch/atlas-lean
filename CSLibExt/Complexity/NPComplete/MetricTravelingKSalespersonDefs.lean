/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# METRIC TRAVELING K-SALESPERSON: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), MINIMUM METRIC TRAVELING K-SALESPERSON PROBLEM (decision version);
G. N. Frederickson, M. S. Hecht, and C. E. Kim, "Approximation algorithms for some routing
problems", SIAM Journal on Computing 7 (1978), 178-193, doi:10.1137/0207017 (the k-person
min-max tour problem);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND22] TRAVELING SALESMAN (NP-complete with
distances in `{1, 2}`, which satisfy the triangle inequality).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TravelingRepairmanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MetricTravelingKSalesperson

open TravelingRepairman (TravelingRepairmanInstance routeLength)

/-- An instance: the number `m` of cities, the distance matrix as `m` rows of `m` entries
(`d(a, b)` is entry `b` of row `a`), the initial city `s`, the number `k` of subtours, and the
bound `K`. -/
abbrev MetricTravelingKSalespersonInstance := ℕ × List (List ℕ) × ℕ × ℕ × ℕ

/-- The metric part of an instance, as a `TravelingRepairmanWanted` instance (cities, matrix,
initial city, bound). -/
def toMetric (i : MetricTravelingKSalespersonInstance) : TravelingRepairmanInstance :=
  (i.1, i.2.1, i.2.2.1, i.2.2.2.2)

/-- Well-formedness of an instance: the distances form a metric on the `m` cities and `s < m`
(`TravelingRepairman.WellFormed`), distances between distinct cities are positive, `0 < k`, and
`0 < K`. -/
def WellFormed (i : MetricTravelingKSalespersonInstance) : Prop :=
  TravelingRepairman.WellFormed (toMetric i) ∧
    (∀ a < i.1, ∀ b < i.1, a ≠ b → 0 < TravelingRepairman.dist (toMetric i) a b) ∧
    0 < i.2.2.2.1 ∧ 0 < i.2.2.2.2

/-- Some collection of at most `k` subtours, each a list of distinct cities starting at `s`
whose closed route back to `s` has length at most `K`, contains every city. -/
def MetricTravelingKSalespersonFeasible (i : MetricTravelingKSalespersonInstance) : Prop :=
  ∃ tours : List (List ℕ), tours.length ≤ i.2.2.2.1 ∧
    (∀ t ∈ tours, t.head? = some i.2.2.1 ∧ t.Nodup ∧ (∀ c ∈ t, c < i.1) ∧
      routeLength (toMetric i) (t ++ [i.2.2.1]) ≤ i.2.2.2.2) ∧
    ∀ c < i.1, ∃ t ∈ tours, c ∈ t

open Classical in
/-- METRIC TRAVELING K-SALESPERSON as a decision problem over bitstrings. -/
noncomputable def metricTravelingKSalespersonDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MetricTravelingKSalespersonInstance) x with
  | some i => decide (WellFormed i ∧ MetricTravelingKSalespersonFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MetricTravelingKSalesperson
