/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Bernoulli.EulerValueSumModPrime
public import MathlibExt.NumberTheory.Bernoulli.PolyBernoulliPoly
public import MathlibExt.NumberTheory.Bernoulli.StirlingHarmonic
public import MathlibExt.NumberTheory.Bernoulli.SumModPrime
public import MathlibExt.NumberTheory.Bernoulli.SumPolyBernoulli
public import MathlibExt.NumberTheory.Bernoulli.TruncatedSumModPrime
public import MathlibExt.NumberTheory.Bernoulli.WeightedSum
public import WantedExt.NumberTheory.EulerPolynomialFormulasWanted
public import WantedExt.NumberTheory.GobelSequenceWanted
public import Mathlib.NumberTheory.Harmonic.Defs
public import MathlibExt.NumberTheory.BernoulliStirlingHarmonicPrimeMulSumBernoulliDivModPrime
public import MathlibExt.NumberTheory.BernoulliStirlingHarmonicSumBernoulliHarmonicPowerIdentity

/-
Statements of the same source proved in modules this file imports:
`MathlibExt.NumberTheory.Bernoulli.WeightedSum` (Corollary 2, equation (14)),
`MathlibExt.NumberTheory.Bernoulli.SumPolyBernoulli` (Corollary 3),
`MathlibExt.NumberTheory.Bernoulli.SumModPrime` (Corollary 4, equation (23),
`sum_prime_mul_bernoulli_mod_prime`),
`MathlibExt.NumberTheory.Bernoulli.TruncatedSumModPrime` (Corollary 4, equation (24)), and
`MathlibExt.NumberTheory.Bernoulli.EulerValueSumModPrime` (Corollary 4, equation (25)).
-/

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

end

end MetaMathlibExt
