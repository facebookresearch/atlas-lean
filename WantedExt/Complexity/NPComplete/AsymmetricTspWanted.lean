/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TRAVELING SALESPERSON (ASYMMETRIC) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), TRAVELING SALESPERSON
PROBLEM (asymmetric).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.AsymmetricTspDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AsymmetricTsp

/-!
# TRAVELING SALESPERSON (ASYMMETRIC) is NP-complete

An integer-weighted complete directed graph, given by a weight matrix with zero diagonal (not
assumed symmetric), and a bound `B`. The question is whether there is a directed tour visiting
every vertex exactly once whose total weight, including the return to the start, is at most
`B`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **TRAVELING SALESPERSON (ASYMMETRIC) is NP-complete.** The asymmetric traveling salesperson
decision problem belongs to NP, and every decision problem in NP reduces to it by a
polynomial-time many-one reduction.

Source: M. R. Garey and D. S.
Johnson, *Computers and Intractability* (1979), TRAVELING SALESPERSON PROBLEM
(asymmetric). -/
public theorem_wanted asymmetricTsp_npComplete :
    asymmetricTspDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L asymmetricTspDec

end MetaMathlibExt.Complexity.NPComplete.AsymmetricTsp
