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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

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

/-- An instance: the trips as pairs `(σ_i, τ_i)`, the travel-time matrix `θ` and the
consecutive-trip cost matrix `c` as lists of rows, the depots as triples
`(r_d, [o_{d0}, …, o_{d(n-1)}], [e_{0d}, …, e_{(n-1)d}])`, and the bound `B`. -/
abbrev MultipleDepotVehicleSchedulingInstance :=
  List (ℕ × ℕ) × List (List ℕ) × List (List ℕ) × List (ℕ × List ℕ × List ℕ) × ℕ

/-- The number `n` of trips. -/
def numTrips (i : MultipleDepotVehicleSchedulingInstance) : ℕ := i.1.length

/-- The depots of the instance. -/
def depots (i : MultipleDepotVehicleSchedulingInstance) : List (ℕ × List ℕ × List ℕ) :=
  i.2.2.2.1

/-- Well-formedness of an instance: at least two depots, `σ_i < τ_i` for every trip, `θ` and
`c` are `n × n` matrices, and every depot lists `n` pull-out and `n` pull-in costs. -/
def WellFormed (i : MultipleDepotVehicleSchedulingInstance) : Prop :=
  2 ≤ (depots i).length ∧ (∀ p ∈ i.1, p.1 < p.2) ∧
    i.2.1.length = numTrips i ∧ (∀ row ∈ i.2.1, row.length = numTrips i) ∧
    i.2.2.1.length = numTrips i ∧ (∀ row ∈ i.2.2.1, row.length = numTrips i) ∧
    ∀ d ∈ depots i, d.2.1.length = numTrips i ∧ d.2.2.length = numTrips i

/-- Trips `a, b` form a feasible pair: `τ_a + θ_{ab} ≤ σ_b`. -/
def FeasiblePair (i : MultipleDepotVehicleSchedulingInstance) (a b : ℕ) : Prop :=
  (i.1.getD a (0, 0)).2 + (i.2.1.getD a []).getD b 0 ≤ (i.1.getD b (0, 0)).1

/-- The cost of the vehicle schedule `trips` of depot `d`: the pull-out cost to its first trip,
the costs `c_{ab}` of its consecutive trips, and the pull-in cost from its last trip. -/
def scheduleCost (i : MultipleDepotVehicleSchedulingInstance) (d : ℕ) (trips : List ℕ) : ℕ :=
  let D := (depots i).getD d (0, [], [])
  D.2.1.getD (trips.headD 0) 0 +
    ((trips.zip trips.tail).map (fun p => (i.2.2.1.getD p.1 []).getD p.2 0)).sum +
      D.2.2.getD (trips.getLastD 0) 0

/-- There is a list of vehicle schedules `(d, trips)`, each a nonempty chain of feasible pairs
at an existing depot `d`, covering every trip exactly once, with at most `r_d` schedules at
every depot `d` and total cost at most `B`. -/
def MultipleDepotVehicleSchedulingFeasible (i : MultipleDepotVehicleSchedulingInstance) :
    Prop :=
  ∃ duties : List (ℕ × List ℕ),
    (∀ D ∈ duties, D.1 < (depots i).length ∧ D.2 ≠ [] ∧ D.2.IsChain (FeasiblePair i)) ∧
    (duties.flatMap Prod.snd).Perm (List.range (numTrips i)) ∧
    (∀ d < (depots i).length,
      (duties.filter (fun D => D.1 = d)).length ≤ ((depots i).getD d (0, [], [])).1) ∧
    (duties.map (fun D => scheduleCost i D.1 D.2)).sum ≤ i.2.2.2.2

open Classical in
/-- MULTIPLE-DEPOT VEHICLE SCHEDULING as a decision problem over bitstrings. -/
noncomputable def multipleDepotVehicleSchedulingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipleDepotVehicleSchedulingInstance) x with
  | some i => decide (WellFormed i ∧ MultipleDepotVehicleSchedulingFeasible i)
  | none => false

/-- **MULTIPLE-DEPOT VEHICLE SCHEDULING is NP-complete.** Source: Bertossi, Carraresi and
Gallo (1987); Olariu and Frăsinaru (2020). -/
public theorem_wanted multipleDepotVehicleScheduling_npComplete :
    multipleDepotVehicleSchedulingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multipleDepotVehicleSchedulingDec

end MetaMathlibExt.Complexity.NPComplete.MultipleDepotVehicleScheduling
