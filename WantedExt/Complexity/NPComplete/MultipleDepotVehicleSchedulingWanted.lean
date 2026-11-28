/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE-DEPOT VEHICLE SCHEDULING is NP-complete

Source:
A. A. Bertossi, P. Carraresi and G. Gallo, "On some matching problems arising in vehicle
scheduling models", Networks 17 (1987), 271-281, doi:10.1002/net.3230170303;
E. F. Olariu and C. Frăsinaru, "Multiple-depot vehicle scheduling problem heuristics",
arXiv:2004.14951 (2020), Section 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultipleDepotVehicleSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleDepotVehicleScheduling

/-!
# MULTIPLE-DEPOT VEHICLE SCHEDULING is NP-complete

INSTANCE: trips `T_0, …, T_{n-1}`, trip `T_i` with starting time `σ_i` and ending time
`τ_i > σ_i`; the time `θ_{ij}` a vehicle needs from the end location of `T_i` to the start
location of `T_j`; the cost `c_{ij}` of a vehicle performing `T_j` right after `T_i`;
`m ≥ 2` depots, depot `D_d` with `r_d` available vehicles, a pull-out cost `o_{di}` from
`D_d` to trip `T_i` and a pull-in cost `e_{id}` from `T_i` back to `D_d`; and a bound `B`.
QUESTION: can the trips be partitioned into vehicle schedules, each a nonempty sequence of
trips in which every two consecutive trips `T_i, T_j` form a feasible pair
(`τ_i + θ_{ij} ≤ σ_j`), each starting and ending its duty at one depot, using at most `r_d`
vehicles of every depot `D_d`, with total cost (pull-out, consecutive-trip and pull-in costs)
at most `B`?

The model is the multiple-depot vehicle scheduling problem (MDVSP) as defined by Olariu and
Frăsinaru, Section 1, who record that it is NP-hard when there are at least two depots
(Bertossi, Carraresi and Gallo); with one depot it is polynomial, so `m ≥ 2` is part of the
instance class. Trips take positive time, so every feasible pair `T_i, T_j` has `σ_i < σ_j`
and vehicle schedules follow the timetable. A list of vehicle schedules, each tagged with its
depot, is a certificate checkable in polynomial time. Trips and depots are numbered from `0`
below; all numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MULTIPLE-DEPOT VEHICLE SCHEDULING is NP-complete.** Source: Bertossi, Carraresi and
Gallo (1987); Olariu and Frăsinaru (2020). -/
public theorem_wanted multipleDepotVehicleScheduling_npComplete :
    multipleDepotVehicleSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipleDepotVehicleSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.MultipleDepotVehicleScheduling
