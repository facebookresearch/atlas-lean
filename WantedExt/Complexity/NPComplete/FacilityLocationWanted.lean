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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FacilityLocationDefs

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
