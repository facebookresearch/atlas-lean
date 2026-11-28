/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 2-near perfect numbers of the forms `2^k p` and `2^k p^2`

Statements from Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua
Zelinsky, *On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61 (arXiv:2310.01305).
Labels follow the journal numbering; the arXiv version numbers Lemmas 1-10 as Lemmas 3-7,
10, 11, 14, 15, 17 and Propositions 1-5 as Propositions 8, 9, 12, 13, 16.

A number `n` is `2`-near perfect with omitted divisors `d₁ ≠ d₂` when `d₁, d₂ ∣ n` and
`σ(n) = 2n + d₁ + d₂`. It is strongly `2`-near perfect when it has a divisor `d` with
`σ(n) = 2n + d + n / d` (the paper's equivalent form of the definition); for `n = 2^k p`
with `p` odd, `d ≠ n / d` holds automatically. The classification of strongly `2`-near
perfect numbers of the form `2^k p`
(`strong_two_near_perfect_two_pow_mul_prime_classification`) is proved in
`MathlibExt.NumberTheory.TwoNearPerfectStrongTwoNearPerfectTwoPowMulPrimeClassification`.
Exponents flattened in the extracted statements (`2k+1`, `pk`) are read as powers, as in
the paper.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import MathlibExt.NumberTheory.NearPerfectPowerTwoDivisibility
public import MathlibExt.NumberTheory.StrongTwoNearPerfectExponentBound
public import MathlibExt.NumberTheory.TwoNearPerfectEquationDivisibility
public import MathlibExt.NumberTheory.TwoNearPerfectEquationSeven
public import MathlibExt.NumberTheory.TwoNearPerfectEquationSix
public import MathlibExt.NumberTheory.TwoNearPerfectOddDivisor
public import MathlibExt.NumberTheory.TwoNearPerfectOmittedDivisors
public import MathlibExt.NumberTheory.TwoNearPerfectPowerOfTwoDivisors
public import MathlibExt.NumberTheory.TwoNearPerfect
public import MathlibExt.NumberTheory.TwoNearPerfectTwoNearPerfectTwoPowMulPrimeSq
public import MathlibExt.NumberTheory.TwoNearPerfectTwoNearPerfectTwoPowMulPrimeSqCaseThree
public import MathlibExt.NumberTheory.TwoNearPerfectTwoNearPerfectTwoPowMulPrimeCases
public import MathlibExt.NumberTheory.TwoNearPerfectTwoNearPerfectTwoPowMulPrimeSqCaseFive
public import MathlibExt.NumberTheory.TwoNearPerfectStrongTwoNearPerfectTwoPowMulPrimeClassification

namespace MetaMathlibExt

@[expose] public section

end

end MetaMathlibExt
