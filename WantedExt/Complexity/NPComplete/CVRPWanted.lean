/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CAPACITATED VEHICLE ROUTING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), VEHICLE ROUTING
(capacitated); G. B. Dantzig and J. H. Ramser, "The truck dispatching problem" (1959).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CVRP

/-!
# CAPACITATED VEHICLE ROUTING is NP-complete

Customers with demands, integer travel costs between customers and a depot, a number of
vehicles, a per-route capacity, and a total length bound. Customers are `0, …, n - 1` and the
depot is index `n`. The question is whether all customers can be served by at most `m` depot-
returning routes, each within capacity, of total length at most `K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A CVRP instance: customer count, demands, distance matrix (including depot), vehicle
count, capacity, total length bound. -/
abbrev CVRPInstance := ℕ × List ℕ × List (List ℕ) × ℕ × ℕ × ℕ


/-- Length of one depot-returning route: depot to first, consecutive, last to depot. -/
def RouteLength (dist : List (List ℕ)) (depot : ℕ) (route : List ℕ) : ℕ :=
  match route with
  | [] => 0
  | first :: _ =>
    (dist.getD depot []).getD first 0 +
    ((List.zip route route.tail).map (fun p => (dist.getD p.1 []).getD p.2 0)).sum +
    (dist.getD (route.getLast?.getD depot) []).getD depot 0


/-- Well-formedness of an instance. -/
def WellFormed (i : CVRPInstance) : Prop :=
  i.2.1.length = i.1 ∧ i.2.2.1.length = i.1 + 1 ∧
    ∀ row ∈ i.2.2.1, row.length = i.1 + 1

/-- At most `m` routes within capacity of total length at most `K`. -/
def CVRPFeasible
    (i : CVRPInstance) : Prop :=
  ∃ routes : List (List ℕ), routes.length ≤ i.2.2.2.1 ∧
    (∀ route ∈ routes, route.Nodup ∧ ∀ c ∈ route, c < i.1) ∧
    (∀ c < i.1, ∃ route ∈ routes, c ∈ route ∧
      ∀ route' ∈ routes, c ∈ route' → route' = route) ∧
    (∀ route ∈ routes, (route.map (fun c => i.2.1.getD c 0)).sum ≤ i.2.2.2.2.1) ∧
    (routes.map (fun route => RouteLength i.2.2.1 i.1 route)).sum ≤ i.2.2.2.2.2

open Classical in
/-- CAPACITATED VEHICLE ROUTING as a decision problem over bitstrings. -/
noncomputable def cvrpDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CVRPInstance) x with
  | some i => decide (WellFormed i ∧ CVRPFeasible i)
  | none => false

/-- **CAPACITATED VEHICLE ROUTING is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), VEHICLE ROUTING (capacitated); G. B. Dantzig and J.
H. Ramser, "The truck dispatching problem" (1959). -/
public theorem_wanted cvrp_npComplete :
    cvrpDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cvrpDec

end MetaMathlibExt.Complexity.NPComplete.CVRP
