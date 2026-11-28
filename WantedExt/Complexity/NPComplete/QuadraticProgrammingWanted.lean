/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# QUADRATIC PROGRAMMING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP2] QUADRATIC PROGRAMMING;
S. Sahni, "Computationally related problems", SIAM Journal on Computing 3 (1974), 262-279,
doi:10.1137/0203021 (NP-hardness);
S. A. Vavasis, "Quadratic programming is in NP", Information Processing Letters 36 (1990),
73-77, doi:10.1016/0020-0190(90)90100-C (membership in NP).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.QuadraticProgrammingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.QuadraticProgramming

/-!
# QUADRATIC PROGRAMMING is NP-complete

Given a finite set `X` of pairs `(x, b)`, where `x` is an `m`-tuple of rational numbers and `b`
is a rational number, two `m`-tuples `c` and `d` of rational numbers, and a rational number `B`,
is there an `m`-tuple `y` of rational numbers such that `x · y ≤ b` for all `(x, b) ∈ X` and
`∑ᵢ (cᵢ yᵢ² + dᵢ yᵢ) ≥ B`?

A rational number is encoded as `((p, q), r)` with value `(p - q) / r` and `r > 0`
(`WellFormed`): an integer numerator as a pair of naturals `(positive part, negative part)`,
as in `ZeroOneILPWanted`, over a positive denominator. All numbers use the canonical binary
encoding.

Garey and Johnson record the problem as NP-hard and not known to be in NP; Vavasis (1990)
proved membership in NP, so it is NP-complete.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **QUADRATIC PROGRAMMING is NP-complete.** Source: Garey and Johnson (1979), [MP2];
Sahni (1974); Vavasis (1990). -/
public theorem_wanted quadraticProgramming_npComplete :
    quadraticProgrammingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L quadraticProgrammingDec

end MetaMathlibExt.Complexity.NPComplete.QuadraticProgramming
