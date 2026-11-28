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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MetricFacilityLocationDefs

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

/-- **METRIC FACILITY LOCATION is NP-complete.** Source: Guha and Khuller (1999); Crescenzi and
Kann, MINIMUM FACILITY LOCATION. -/
public theorem_wanted metricFacilityLocation_npComplete :
    metricFacilityLocationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L metricFacilityLocationDec

end MetaMathlibExt.Complexity.NPComplete.MetricFacilityLocation
