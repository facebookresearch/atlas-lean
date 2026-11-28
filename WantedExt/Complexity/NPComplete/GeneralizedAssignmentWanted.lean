/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED ASSIGNMENT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), GENERALIZED ASSIGNMENT
PROBLEM.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GeneralizedAssignmentDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedAssignment

/-!
# GENERALIZED ASSIGNMENT is NP-complete

Jobs with per-machine resource consumptions and assignment costs, per-machine capacities, and a
cost bound `K`. The question is whether every job can be assigned to one machine so that no
machine's capacity is exceeded and the total assignment cost is at most `K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GENERALIZED ASSIGNMENT is NP-complete.** The generalized assignment decision problem
belongs to NP, and every decision problem in NP reduces to it by a polynomial-time many-one
reduction.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), GENERALIZED ASSIGNMENT PROBLEM. -/
public theorem_wanted generalizedAssignment_npComplete :
    generalizedAssignmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L generalizedAssignmentDec

end MetaMathlibExt.Complexity.NPComplete.GeneralizedAssignment
