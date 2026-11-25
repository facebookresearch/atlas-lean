/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import MathlibExt.NumberTheory.AACarmichaelAuxiliaryPrimes
public import MathlibExt.NumberTheory.AACarmichaelAuxiliaryProduct
public import MathlibExt.NumberTheory.AACarmichaelGcd

namespace MetaMathlibExt

@[expose] public section

/-- **Conditional lower bound for $(a, a)$-Carmichael numbers with prescribed gcd.** Assume
Conjecture 2: there are a real number $A \ge 2$ and a natural number $l_0$ such that for every
natural number $l \ge l_0$ and every integer $b$ with $\gcd(b, l) = 1$ there is a prime $p$ with
$p \equiv b \pmod{l}$ and $p < l (\log l)^A$. Let $a$ be an integer and $\nu$ a positive integer
with $\gcd(a, \nu) = 1$ and $a + \nu$ odd. For real $X$ let $C_\nu(X, a)$ be the number of
$(a, a)$-Carmichael numbers $n \le X$ for which the nonnegative greatest common divisor of the
integers $p - a$, over the primes $p$ dividing $n$, equals $\nu$. Then for every $\varepsilon > 0$
and all sufficiently large real $X$,
$$C_\nu(X, a) \ge X^{1 - (2 + \varepsilon) \log\log\log\log X / \log\log\log X}.$$

This is the paper's bound $C_\nu(X, a) \ge X^{1 - (2 + o(1)) \log\log\log\log X / \log\log\log X}$,
with $2 + \varepsilon$ in place of $2 + o(1)$.

Source: definitions of $C_\nu(X, a)$ and Conjecture 2 read from the arXiv version
(arXiv:2607.02738); the theorem's journal wording matches it.

Source: Thomas Wright, *(a,a)-Carmichael Numbers and Greatest Common Divisors of p-a*,
INTEGERS 26 (2026), Article A123, Theorem 1 (`integers-2026-A123-thm-1`). -/
public theorem_wanted aaCarmichael_count_ge_of_least_prime_in_progression_bound
    (hconj : ∃ A : ℝ, 2 ≤ A ∧ ∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l → ∀ b : ℤ, Int.gcd b l = 1 →
      ∃ p : ℕ, p.Prime ∧ (p : ℤ) ≡ b [ZMOD l] ∧ (p : ℝ) < l * Real.log l ^ A)
    (a : ℤ) (ν : ℕ) (hν : 0 < ν) (hcop : Int.gcd a ν = 1) (hpar : Odd (a + ν))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      X ^ (1 - (2 + ε) * Real.log (Real.log (Real.log (Real.log X))) /
          Real.log (Real.log (Real.log X))) ≤
        ({n : ℕ | (n : ℝ) ≤ X ∧ IsAACarmichael a n ∧
            n.primeFactors.gcd (fun p => (p : ℤ) - a) = ν}.ncard : ℝ)

end

end MetaMathlibExt
