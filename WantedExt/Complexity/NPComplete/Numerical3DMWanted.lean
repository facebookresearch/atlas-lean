/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NUMERICAL 3-DIMENSIONAL MATCHING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), NUMERICAL 3-DIMENSIONAL
MATCHING (strongly NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.Numerical3DMDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Numerical3DM

/-!
# NUMERICAL 3-DIMENSIONAL MATCHING is NP-complete

Three lists `A, B, C` of the same length `n` and a common target `B`. The question is whether
permutations `p, q` satisfy `A_i + B_{p(i)} + C_{q(i)} = Target` for every `i`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **NUMERICAL 3-DIMENSIONAL MATCHING is NP-complete.** The decision problem NUMERICAL
3-DIMENSIONAL MATCHING belongs to NP, and every decision problem in NP reduces to it by a
polynomial-time many-one reduction.

Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), NUMERICAL 3-DIMENSIONAL MATCHING (strongly
NP-complete). -/
public theorem_wanted numerical3DM_npComplete :
    numerical3DMDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L numerical3DMDec

end MetaMathlibExt.Complexity.NPComplete.Numerical3DM
