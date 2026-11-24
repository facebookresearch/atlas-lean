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

/-- **Facility location instances.** A facility location instance is a triple $(o, D, B)$ made of
a finite list $o$ of natural numbers (the opening costs of the facilities), a finite list $D$ of
finite lists of natural numbers (the $c$-th list holds the costs of assigning client $c$ to each
facility), and a natural number $B$ (the budget). -/
abbrev FacilityLocationInstance := List ℕ × List (List ℕ) × ℕ

/-- **Well-formed facility location instances.** A facility location instance $(o, D, B)$, with
opening costs $o$ and assignment-cost rows $D$, is well-formed when every row of $D$ has the same
length as $o$. -/
def WellFormed (i : FacilityLocationInstance) : Prop :=
  ∀ row ∈ i.2.1, row.length = i.1.length

/-- **Feasible facility location instances.** Let $(o, D, B)$ be a facility location instance
with opening costs $o = (o_0, \dots, o_{n-1})$, assignment-cost rows $D = (D_0, \dots, D_{m-1})$
and budget $B$, and write $D_{c,j}$ for the $j$-th entry of the row $D_c$, read as $0$ when $D_c$
has no $j$-th entry. The instance is feasible when there is a map $\sigma$ from the clients
$\{0, \dots, m-1\}$ to the facilities $\{0, \dots, n-1\}$ such that the opening costs of the
facilities in the image of $\sigma$ plus the assignment costs stay within the budget:
$\sum_{j \in \sigma(\{0, \dots, m-1\})} o_j + \sum_{c=0}^{m-1} D_{c,\sigma(c)} \le B$. -/
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
/-- **The FACILITY LOCATION decision problem.** FACILITY LOCATION is the decision problem that
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a
facility location instance that is well-formed and feasible; bitstrings that do not decode to an
instance are rejected. -/
noncomputable def facilityLocationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FacilityLocationInstance) x with
  | some i => decide (WellFormed i ∧ FacilityLocationFeasible i)
  | none => false

/-- **FACILITY LOCATION is NP-complete.** FACILITY LOCATION belongs to NP, and every decision
problem $L$ in NP reduces to FACILITY LOCATION by a polynomial-time many-one reduction: there is
a polynomial-time computable map $f$ on bitstrings such that, for every bitstring $x$, $L$
accepts $x$ exactly when FACILITY LOCATION accepts $f(x)$.

Source: G. Cornuéjols, G. L. Nemhauser, and L. A.
Wolsey, "The uncapacitated facility location problem", in P. B. Mirchandani and R. L.
Francis, eds., Discrete Location Theory, Wiley, 1990, 119-171. -/
public theorem_wanted facilityLocation_npComplete :
    facilityLocationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L facilityLocationDec

end MetaMathlibExt.Complexity.NPComplete.FacilityLocation
