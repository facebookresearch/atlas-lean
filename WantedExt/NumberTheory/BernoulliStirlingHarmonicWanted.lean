/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
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

/-
Statements of the same source proved in modules this file imports:
`MathlibExt.NumberTheory.Bernoulli.WeightedSum` (Corollary 2, equation (14)),
`MathlibExt.NumberTheory.Bernoulli.SumPolyBernoulli` (Corollary 3),
`MathlibExt.NumberTheory.Bernoulli.SumModPrime` (Corollary 4, equation (23),
`sum_prime_mul_bernoulli_mod_prime`), and
`MathlibExt.NumberTheory.Bernoulli.TruncatedSumModPrime` (Corollary 4, equation (24)).
-/

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

/--
**A Bernoulli–harmonic power-sum identity.** Let $B_j$ denote the Bernoulli numbers with
$B_1 = -\tfrac12$, and let $H_m = \sum_{i=1}^{m} 1/i$ denote the harmonic numbers. For all
positive integers $n$ and $m$,
$$\sum_{j=1}^{n} \left(\binom{n}{j} - 1\right) \frac{B_j}{j} m^{n-j} =
m^n (H_m - H_n) - \sum_{j=1}^{m} \frac{(m-j)^n}{j}.$$

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 1,
equation (11).
-/
public theorem_wanted sum_bernoulli_harmonic_power_identity (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) :
    (∑ j ∈ Finset.Icc 1 n,
      ((n.choose j : ℚ) - 1) * (bernoulli j / (j : ℚ)) * (m : ℚ) ^ (n - j)) =
      (m : ℚ) ^ n * (harmonic m - harmonic n) -
        ∑ j ∈ Finset.Icc 1 m, ((m - j : ℕ) : ℚ) ^ n / (j : ℚ)

/--
**The congruence $\sum_{j=0}^{p} E_j(0) \equiv 3/2 \pmod p$.** Let $E_j(x)$ denote the Euler
polynomials. For every odd prime $p$, the rational number $S = E_0(0) + E_1(0) + \dots + E_p(0)$
has denominator not divisible by $p$, and its residue modulo $p$ (its numerator times the
inverse of its denominator in $\mathbb{Z}/p\mathbb{Z}$) equals $3 \cdot 2^{-1}$.

The values $E_j(0)$ are the Euler numbers of the source; they come from the generating function
$2e^{xt}/(e^t + 1)$ and begin $1, -\tfrac12, 0, \tfrac14$.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 4,
equation (25).
-/
public theorem_wanted sum_euler_eval_zero_mod_prime (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬p ∣ (∑ j ∈ Finset.range (p + 1), (eulerPoly j).eval 0).den ∧
      ratResidue p (∑ j ∈ Finset.range (p + 1), (eulerPoly j).eval 0) =
        ratResidue p (3 / 2)

end

end MetaMathlibExt
