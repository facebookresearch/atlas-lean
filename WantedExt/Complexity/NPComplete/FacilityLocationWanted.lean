/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FACILITY LOCATION is NP-complete

Source:
G. Cornuéjols, G. L. Nemhauser, and L. A. Wolsey, "The uncapacitated facility location
problem", in P. B. Mirchandani and R. L. Francis, eds., Discrete Location Theory, Wiley, 1990,
119-171.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FacilityLocation

/-!
# FACILITY LOCATION is NP-complete

Facilities with opening costs and clients with assignment costs to each facility, and a budget
`B`. The question is whether facilities can be opened and every client assigned to an open
facility with total cost (opening plus assignment) at most `B`. Costs are natural numbers (a
finite rationally-encoded decision version).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A facility-location instance: opening costs, assignment costs (client by facility),
budget. -/
abbrev FacilityLocationInstance := List ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : FacilityLocationInstance) : Prop :=
  ∀ row ∈ i.2.1, row.length = i.1.length

/-- An assignment of total cost at most `B`. -/
def FacilityLocationFeasible
    (i : FacilityLocationInstance) : Prop :=
  ∃ assign : List ℕ, assign.length = i.2.1.length ∧
    (∀ c < i.2.1.length, assign.getD c 0 < i.1.length) ∧
    ∃ used : List ℕ, used.Nodup ∧
      (∀ f ∈ used, ∃ c < i.2.1.length, assign.getD c 0 = f) ∧
      (∀ c < i.2.1.length, assign.getD c 0 ∈ used) ∧
      (used.map (fun f => i.1.getD f 0)).sum +
        (Finset.range i.2.1.length).sum
          (fun c => (i.2.1.getD c []).getD (assign.getD c 0) 0) ≤ i.2.2

open Classical in
/-- FACILITY LOCATION as a decision problem over bitstrings. -/
noncomputable def facilityLocationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FacilityLocationInstance) x with
  | some i => decide (WellFormed i ∧ FacilityLocationFeasible i)
  | none => false

/-- **FACILITY LOCATION is NP-complete.** Source: G. Cornuéjols, G. L. Nemhauser, and L. A.
Wolsey, "The uncapacitated facility location problem", in P. B. Mirchandani and R. L.
Francis, eds., Discrete Location Theory, Wiley, 1990, 119-171. -/
public theorem_wanted facilityLocation_npComplete :
    facilityLocationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L facilityLocationDec

end MetaMathlibExt.Complexity.NPComplete.FacilityLocation
