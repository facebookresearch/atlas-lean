/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# QUADRATIC CONGRUENCES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN1] QUADRATIC
CONGRUENCES;
K. L. Manders and L. M. Adleman, "NP-complete decision problems for binary
quadratics", Journal of Computer and System Sciences 16 (1978), 168-184,
doi:10.1016/0022-0000(78)90044-2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.QuadraticCongruencesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.QuadraticCongruences

/-!
# QUADRATIC CONGRUENCES is NP-complete

INSTANCE: positive integers `a`, `b` and `c`. QUESTION: is there a positive integer `x < c`
such that `x² ≡ a (mod b)`?

The numbers use the canonical binary encoding; the problem is NP-complete in the weak sense
(trying every `x < c` takes time pseudo-polynomial in `c`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **QUADRATIC CONGRUENCES is NP-complete.** Source: Garey and Johnson (1979), [AN1];
Manders and Adleman (1978). -/
public theorem_wanted quadraticCongruences_npComplete :
    quadraticCongruencesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L quadraticCongruencesDec

end MetaMathlibExt.Complexity.NPComplete.QuadraticCongruences
