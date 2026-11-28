/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BINARY QUADRATIC DIOPHANTINE EQUATIONS is NP-complete

Source:
J. C. Lagarias, "Succinct certificates for the solvability of binary quadratic Diophantine
equations", Proceedings of the 20th Annual Symposium on Foundations of Computer Science (FOCS
1979), 47-54, doi:10.1109/SFCS.1979.40 (full version arXiv:math/0611209, Theorem 1.2(ii): the
set of `a, b, c, d, e, f ∈ ℤ` such that `a x₁² + b x₁ x₂ + c x₂² + d x₁ + e x₂ + f = 0` has a
solution in nonnegative integers is in NP, and with Manders and Adleman's result "testing
membership in the sets Σ₁ and Σ₂ in Theorem 1.2 are both NP-complete");
K. L. Manders and L. Adleman, "NP-complete decision problems for binary quadratics", Journal of
Computer and System Sciences 16 (1978), 168-184, doi:10.1016/0022-0000(78)90044-2 (the special
form `α x² + β y - γ = 0` with natural-number solutions is NP-complete);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [AN8] QUADRATIC DIOPHANTINE EQUATIONS (the
special form).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BinaryQuadraticDiophantineDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BinaryQuadraticDiophantine

/-!
# BINARY QUADRATIC DIOPHANTINE EQUATIONS is NP-complete

INSTANCE: integers `a, b, c, d, e, f`. QUESTION: are there nonnegative integers `x₁, x₂` with
`a x₁² + b x₁ x₂ + c x₂² + d x₁ + e x₂ + f = 0`?

This is Lagarias's set `Σ₂`. Each integer is a pair of naturals `(positive part, negative part)`
denoting their difference, in binary. The smallest solution can be exponentially long in the
input, so membership in NP is Lagarias's theorem, not a direct certificate. Lagarias also shows
that the variant with unrestricted integer solutions (his `Σ₃`) is in NP, but NP-completeness
is stated, and proved, only for nonnegative solutions, which this module formalizes.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BINARY QUADRATIC DIOPHANTINE EQUATIONS is NP-complete.** Source: Lagarias (1979), Theorem
1.2(ii); Manders and Adleman (1978); Garey and Johnson (1979), [AN8] (the special form). -/
public theorem_wanted binaryQuadraticDiophantine_npComplete :
    binaryQuadraticDiophantineDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L binaryQuadraticDiophantineDec

end MetaMathlibExt.Complexity.NPComplete.BinaryQuadraticDiophantine
