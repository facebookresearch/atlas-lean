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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CVRPDefs

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
