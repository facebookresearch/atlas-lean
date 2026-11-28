/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLOSEST STRING is NP-complete

Source:
J. K. Lanctot et al., "Distinguishing string selection problems" (2003); M. Frances and A.
Litman, "On covering problems of codes" (1997).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ClosestStringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ClosestString

/-!
# CLOSEST STRING is NP-complete

A list of binary strings, all of the same length, and a distance bound `d`. The question is
whether there is a center string of the same length within Hamming distance `d` of every given
string.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CLOSEST STRING is NP-complete.** The CLOSEST STRING decision problem belongs to NP, and
every decision problem in NP has a polynomial-time many-one reduction to it.

Source: J. K. Lanctot et al., "Distinguishing string
selection problems" (2003); M. Frances and A. Litman, "On covering problems of codes"
(1997). -/
public theorem_wanted closestString_npComplete :
    closestStringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L closestStringDec

end MetaMathlibExt.Complexity.NPComplete.ClosestString
