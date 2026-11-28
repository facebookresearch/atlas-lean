/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RESOURCE-CONSTRAINED PROJECT SCHEDULING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), BIN PACKING; J.
Blazewicz, J. K. Lenstra, and A. H. G. Rinnooy Kan, "Scheduling subject to resource
constraints: classification and complexity", Discrete Applied Mathematics 5 (1983), 11-24
(classification).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RCPSPDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RCPSP

/-!
# RESOURCE-CONSTRAINED PROJECT SCHEDULING is NP-complete

Jobs with durations and resource demands, precedence constraints, a single renewable resource
capacity, and a deadline `D`. The question is whether there are start times meeting all
precedence constraints and the deadline, with the total resource demand of simultaneously
active jobs never exceeding the capacity (checked by forbidding an active subset of demand
exceeding capacity at each time). NP-hardness follows from bin packing: items become unit-
duration jobs with demand equal to item size, no precedence, resource capacity equal to bin
capacity, and makespan bound equal to the number of bins.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RESOURCE-CONSTRAINED PROJECT SCHEDULING is NP-complete.** The decision problem
RESOURCE-CONSTRAINED PROJECT SCHEDULING belongs to NP, and every decision problem in NP has a
polynomial-time many-one reduction to it.

Source: M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), BIN PACKING; J.
Blazewicz, J. K. Lenstra, and A. H. G. Rinnooy Kan, "Scheduling subject to resource constraints:
classification and complexity", Discrete Applied Mathematics 5 (1983), 11-24 (classification). -/
public theorem_wanted rcpsp_npComplete :
    rcpspDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rcpspDec

end MetaMathlibExt.Complexity.NPComplete.RCPSP
