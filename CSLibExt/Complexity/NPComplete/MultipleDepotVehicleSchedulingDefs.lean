/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPLE-DEPOT VEHICLE SCHEDULING: definitions

Source:
A. A. Bertossi, P. Carraresi and G. Gallo, "On some matching problems arising in vehicle
scheduling models", Networks 17 (1987), 271-281, doi:10.1002/net.3230170303;
E. F. Olariu and C. Frăsinaru, "Multiple-depot vehicle scheduling problem heuristics",
arXiv:2004.14951 (2020), Section 1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipleDepotVehicleScheduling

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

end MetaMathlibExt.Complexity.NPComplete.MultipleDepotVehicleScheduling
