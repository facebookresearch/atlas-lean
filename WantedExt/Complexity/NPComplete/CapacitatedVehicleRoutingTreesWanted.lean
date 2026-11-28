/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CAPACITATED VEHICLE ROUTING ON TREES is NP-complete

Source:
M. Labbé, G. Laporte and H. Mercure, "Capacitated vehicle routing on trees", Operations
Research 39 (1991), 616-622, doi:10.1287/opre.39.4.616.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CapacitatedVehicleRoutingTreesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CapacitatedVehicleRoutingTrees

/-!
# CAPACITATED VEHICLE ROUTING ON TREES is NP-complete

The problem TCVRP of Labbé, Laporte and Mercure (1991): `T = (V, E)` is a tree with
nonnegative weights associated with each of its vertices, and nonnegative integer edge lengths.
A fleet of vehicles of capacity `Q` is located at the depot, vertex `0` (the source's `v₁`).
Vehicle collection routes start and end at the depot, such that the weight associated with any
given vertex is collected by exactly one vehicle, and the sum of all weights collected by a
vehicle does not exceed `Q`; the objective is a linear combination `α · (number of vehicles) +
β · (total distance traveled)`. The decision form asks, for nonnegative integers `α`, `β` and a
bound `B`, whether some set of routes has objective at most `B`. All numbers are in binary
encoding. Labbé, Laporte and Mercure show that the TCVRP is NP-hard; the coefficients are part
of the instance here, so the stated problem contains every fixed choice of `α` and `β`.

A route is a closed walk at the depot in the tree. Each vertex of positive weight is assigned
to exactly one route, which must visit it (other routes may pass through it without collecting
it); vertices of weight `0` need no collection. The length of a route is the sum of the lengths
of the edges it traverses, with multiplicity.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CAPACITATED VEHICLE ROUTING ON TREES is NP-complete.** Source: Labbé, Laporte and
Mercure (1991). -/
public theorem_wanted capacitatedVehicleRoutingTrees_npComplete :
    capacitatedVehicleRoutingTreesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L capacitatedVehicleRoutingTreesDec

end MetaMathlibExt.Complexity.NPComplete.CapacitatedVehicleRoutingTrees
