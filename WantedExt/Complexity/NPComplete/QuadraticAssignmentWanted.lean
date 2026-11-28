/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# QUADRATIC ASSIGNMENT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), QUADRATIC ASSIGNMENT
PROBLEM; S. Sahni and T. Gonzalez, "P-complete approximation problems" (1976).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.QuadraticAssignmentDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.QuadraticAssignment

/-!
# QUADRATIC ASSIGNMENT is NP-complete

Nonnegative integer flow and distance matrices and a bound `K`. The question is whether some
permutation (assignment of facilities to locations) has total cost at most `K`: the sum over
all pairs of flow times distance between the assigned locations.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **QUADRATIC ASSIGNMENT is NP-complete.** The decision problem QUADRATIC ASSIGNMENT lies in NP,
and every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), QUADRATIC ASSIGNMENT PROBLEM; S. Sahni and T. Gonzalez,
"P-complete approximation problems" (1976). -/
public theorem_wanted quadraticAssignment_npComplete :
    quadraticAssignmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L quadraticAssignmentDec

end MetaMathlibExt.Complexity.NPComplete.QuadraticAssignment
