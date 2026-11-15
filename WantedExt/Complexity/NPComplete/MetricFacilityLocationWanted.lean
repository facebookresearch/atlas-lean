/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# METRIC FACILITY LOCATION is NP-complete

Source:
S. Guha and S. Khuller, "Greedy strikes back: improved facility location algorithms",
J. Algorithms 31 (1999), 228-248, doi:10.1006/jagm.1998.0993 (the metric uncapacitated facility
location problem, proved max SNP-hard);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
problem MINIMUM FACILITY LOCATION (the same instance; its printed objective differs, see
below).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MetricFacilityLocation

/-!
# METRIC FACILITY LOCATION is NP-complete

INSTANCE: a complete graph `G = (V, E)` with costs `c(vᵢ, vⱼ) ∈ ℕ` that are symmetric and satisfy
the triangle inequality, a set `F ⊆ V` of locations where a facility may be built, for each
`v ∈ F` a cost `f(v) ∈ ℕ` of building a facility at `v`, for each location `v ∈ V` a demand
`d(v) ∈ ℕ`, and a positive integer `K`.
QUESTION: is there a set `F' ⊆ F` of locations at which to build facilities such that
`∑_{u ∈ F'} f(u) + ∑_{v ∈ V} d(v) · min_{u ∈ F'} c(u, v) ≤ K`?

This is the decision version of the metric uncapacitated facility location problem as defined
by Guha and Khuller, who prove it max SNP-hard: every location's demand is served by a built
facility, at the cost of the connection times the demand, and each location is served from a
cheapest built facility. The Crescenzi-Kann compendium lists the problem as MINIMUM FACILITY
LOCATION with the same instance, but prints the service cost as
`∑_{u ∈ F'} ∑_{v ∈ V} d(v) · c(u, v)`, which charges every location to every built facility; the
statement follows Guha and Khuller's minimum, not that printed sum. Choosing for each location a
built facility serving it, with the cost bound, is the same as the bound with the minimum, since
serving each location from its cheapest built facility only lowers the cost. The bound is a
positive integer, following the Garey-Johnson convention.

Locations are `0, …, n - 1`; the costs are an `n × n` matrix, symmetric, satisfying the triangle
inequality, and zero exactly on the diagonal (a facility serves its own location at no connection
cost, and distinct locations are at positive cost), as in
`WantedExt.Complexity.NPComplete.MetricKCenterWanted`.
The candidate locations come with their building costs as a list of pairs `(v, f(v))` with
distinct `v`; the facilities built are a sublist of it. A list `a` names, for each location `v`,
the location `a(v)` of the built facility serving it. This is the metric special case, with
demands, of `WantedExt.Complexity.NPComplete.FacilityLocationWanted`, which allows arbitrary
client-facility costs.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances. Costs, demands and the bound use
the canonical binary encoding.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: location count `n`, cost matrix `c`, candidate locations with building costs
`(v, f(v))`, demands `d` and bound `K`. -/
abbrev MetricFacilityLocationInstance :=
  ℕ × List (List ℕ) × List (ℕ × ℕ) × List ℕ × ℕ

/-- The cost `c(u, v)`. -/
def cost (i : MetricFacilityLocationInstance) (u v : ℕ) : ℕ := (i.2.1.getD u []).getD v 0

/-- Well-formedness of an instance: the cost matrix is `n × n`, zero exactly on the diagonal,
symmetric and satisfies the triangle inequality; the candidate locations are distinct locations;
there is one demand per location; and `0 < K`. -/
def WellFormed (i : MetricFacilityLocationInstance) : Prop :=
  i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧
    (∀ u < i.1, ∀ v < i.1, cost i u v = 0 ↔ u = v) ∧
    (∀ u < i.1, ∀ v < i.1, cost i u v = cost i v u) ∧
    (∀ u < i.1, ∀ v < i.1, ∀ w < i.1, cost i u w ≤ cost i u v + cost i v w) ∧
    (i.2.2.1.map Prod.fst).Nodup ∧ (∀ p ∈ i.2.2.1, p.1 < i.1) ∧ i.2.2.2.1.length = i.1 ∧
    0 < i.2.2.2.2

/-- Facilities built at the locations of a sublist `F'` of the candidates, with location `v`
served by the facility at `a(v)`, cost at most `K` in total. -/
def MetricFacilityLocationFeasible (i : MetricFacilityLocationInstance) : Prop :=
  ∃ F' : List (ℕ × ℕ), F'.Sublist i.2.2.1 ∧
    ∃ a : List ℕ, a.length = i.1 ∧ (∀ v < i.1, a.getD v 0 ∈ F'.map Prod.fst) ∧
      (F'.map Prod.snd).sum +
          ((List.range i.1).map fun v => i.2.2.2.1.getD v 0 * cost i (a.getD v 0) v).sum ≤
        i.2.2.2.2

open Classical in
/-- METRIC FACILITY LOCATION as a decision problem over bitstrings. -/
noncomputable def metricFacilityLocationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MetricFacilityLocationInstance) x with
  | some i => decide (WellFormed i ∧ MetricFacilityLocationFeasible i)
  | none => false

/-- **METRIC FACILITY LOCATION is NP-complete.** Source: Guha and Khuller (1999); Crescenzi and
Kann, MINIMUM FACILITY LOCATION. -/
public theorem_wanted metricFacilityLocation_npComplete :
    metricFacilityLocationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L metricFacilityLocationDec

end MetaMathlibExt.Complexity.NPComplete.MetricFacilityLocation
