/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# METRIC TRAVELING K-SALESPERSON is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.TravelingRepairmanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MetricTravelingKSalesperson

open TravelingRepairman (TravelingRepairmanInstance routeLength)

/-!
# METRIC TRAVELING K-SALESPERSON is NP-complete

INSTANCE: a set `C` of `m` cities with an initial city `s ∈ C`, a distance `d(cᵢ, cⱼ) ∈ ℤ⁺` for
each pair of distinct cities, satisfying the triangle inequality, a positive integer `k` of
salespersons, and a positive integer bound `K`. QUESTION: is there a collection of `k` subtours,
each a closed tour that starts and ends at `s`, such that every city lies on at least one
subtour and every subtour has length at most `K`?

This is the decision version of the compendium's MINIMUM METRIC TRAVELING K-SALESPERSON PROBLEM
(measure: the maximum length of the `k` subtours), the min-max `k`-person traveling salesman problem
of Frederickson, Hecht, and Kim (1978), who list it among NP-complete routing problems. With `k = 1`
it is the metric traveling salesman problem, NP-complete by Garey and Johnson [ND22] already with
distances in `{1, 2}`; that is the reduction behind the theorem.

The metric part of the instance (an `m × m` distance matrix with zero diagonal, symmetric,
satisfying the triangle inequality, and `s < m`) is checked by `TravelingRepairmanWanted`'s
`WellFormed`, and its `routeLength` is reused; as in `MetricTravelingSalespersonWanted`,
distances between distinct cities and the bound are positive, and so is `k`. A subtour is listed
as the distinct cities it visits, starting with `s`; its length is that of the closed route back
to `s` (the subtour `[s]` has length `0`). With the triangle inequality, revisiting a city never
shortens a subtour, so distinct cities suffice. The collection has at most `k` subtours: padding
with `[s]` makes "at most" and "exactly" agree, and it keeps certificates short when `k` is
large (`k` is written in binary). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **METRIC TRAVELING K-SALESPERSON is NP-complete.** Source: Crescenzi and Kann, MINIMUM METRIC
TRAVELING K-SALESPERSON PROBLEM; Frederickson, Hecht, and Kim (1978); Garey and Johnson (1979),
[ND22]. -/
public theorem_wanted metricTravelingKSalesperson_npComplete :
    metricTravelingKSalespersonDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L metricTravelingKSalespersonDec

end MetaMathlibExt.Complexity.NPComplete.MetricTravelingKSalesperson
