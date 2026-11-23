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

/-- **Capacitated vehicle routing instances.** A capacitated vehicle routing instance is a tuple
$(n, d, D, m, C, K)$ consisting of a natural number $n$ (the number of customers), a list $d$ of
natural numbers (the demands), a list $D$ of lists of natural numbers (the distance matrix, whose
rows and columns include the depot), and natural numbers $m$ (the number of vehicles), $C$ (the
capacity) and $K$ (the bound on the total length). -/
abbrev CVRPInstance := ℕ × List ℕ × List (List ℕ) × ℕ × ℕ × ℕ


/-- **Length of a route.** Let $D$ be a list of lists of natural numbers, read as a distance
matrix whose entry $D_{u,v}$ is the entry at position $v$ of the row at position $u$ (positions
counted from $0$), or $0$ if there is no such entry, and let $o$ be a natural number, the depot.
The length of the empty route is $0$, and the length of a route given by a list
$(r_1, \dots, r_k)$ of natural numbers with $k \ge 1$ is
$D_{o,r_1} + \sum_{j=1}^{k-1} D_{r_j,r_{j+1}} + D_{r_k,o}$, where the sum is $0$ when $k = 1$. -/
def RouteLength (dist : List (List ℕ)) (depot : ℕ) (route : List ℕ) : ℕ :=
  match route with
  | [] => 0
  | first :: _ =>
    (dist.getD depot []).getD first 0 +
    ((List.zip route route.tail).map (fun p => (dist.getD p.1 []).getD p.2 0)).sum +
    (dist.getD (route.getLast?.getD depot) []).getD depot 0


/-- **Well-formed capacitated vehicle routing instances.** A capacitated vehicle routing instance
$(n, d, D, m, C, K)$ is well formed when the demand list $d$ has length $n$, the distance matrix
$D$ has $n + 1$ rows, and every row of $D$ has length $n + 1$. -/
def WellFormed (i : CVRPInstance) : Prop :=
  i.2.1.length = i.1 ∧ i.2.2.1.length = i.1 + 1 ∧
    ∀ row ∈ i.2.2.1, row.length = i.1 + 1

/-- **Feasibility of a capacitated vehicle routing instance.** Let $(n, d, D, m, C, K)$ be a
capacitated vehicle routing instance, with customers $0, \dots, n - 1$ and depot $n$, and let the
demand $d_c$ of $c$ be the entry of the list $d$ at position $c$ (counting from $0$), or $0$ if
$d$ has no such entry. The instance is feasible when there is a list of at most $m$ routes, each
a list of natural numbers, such that every route has no repeated entries and only entries less
than $n$; every customer $c < n$ lies on some route, and all routes of the list that contain $c$
are equal; the demands of the entries of each route sum to at most $C$; and the lengths of the
routes, for the distance matrix $D$ and depot $n$, sum to at most $K$. -/
def CVRPFeasible
    (i : CVRPInstance) : Prop :=
  ∃ routes : List (List ℕ), routes.length ≤ i.2.2.2.1 ∧
    (∀ route ∈ routes, route.Nodup ∧ ∀ c ∈ route, c < i.1) ∧
    (∀ c < i.1, ∃ route ∈ routes, c ∈ route ∧
      ∀ route' ∈ routes, c ∈ route' → route' = route) ∧
    (∀ route ∈ routes, (route.map (fun c => i.2.1.getD c 0)).sum ≤ i.2.2.2.2.1) ∧
    (routes.map (fun route => RouteLength i.2.2.1 i.1 route)).sum ≤ i.2.2.2.2.2

open Classical in
/-- **Capacitated vehicle routing as a decision problem.** The decision problem CAPACITATED
VEHICLE ROUTING accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding, to a capacitated vehicle routing instance that is well formed and feasible; it rejects
every bitstring that does not decode. -/
noncomputable def cvrpDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CVRPInstance) x with
  | some i => decide (WellFormed i ∧ CVRPFeasible i)
  | none => false

/-- **CAPACITATED VEHICLE ROUTING is NP-complete.** The decision problem CAPACITATED VEHICLE
ROUTING lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to
it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), VEHICLE ROUTING (capacitated); G. B. Dantzig and J.
H. Ramser, "The truck dispatching problem" (1959). -/
public theorem_wanted cvrp_npComplete :
    cvrpDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cvrpDec

end MetaMathlibExt.Complexity.NPComplete.CVRP
