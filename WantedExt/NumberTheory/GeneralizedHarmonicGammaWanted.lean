/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Probability.Distributions.Gamma
public import MathlibExt.NumberTheory.GeneralizedHarmonicGamma

namespace MetaMathlibExt

@[expose] public section

open MeasureTheory ProbabilityTheory

/-- **Binomially weighted sums of generalized harmonic numbers.** Write $[a, b]$ for the unsigned
Stirling number of the first kind, the number of permutations of $a$ elements with exactly $b$
cycles, and, for real $t$ and a natural number $n$, write $H_n^{(t)} = \sum_{k=1}^{n} 1/k^t$ for
the generalized harmonic number. For all natural numbers $m$ and $n$ and every real $\alpha$,
$$\sum_{j=1}^{n-1} \binom{j}{m} H_j^{(\alpha)} = \binom{n}{m+1} H_n^{(\alpha)} -
\frac{1}{(m+1)!} \sum_{r=0}^{m+1} [m+1, r] (-1)^{m+1-r} H_n^{(\alpha-r)}.$$

Source: Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an
Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Proposition 1, Equation (3)
(`integers-2026-A124-prop-1`). -/
public theorem_wanted sum_choose_mul_generalizedHarmonic (m n : ℕ) (α : ℝ) :
    ∑ j ∈ Finset.Ico 1 n, (j.choose m : ℝ) * generalizedHarmonic α j =
      (n.choose (m + 1) : ℝ) * generalizedHarmonic α n -
        ((m + 1).factorial : ℝ)⁻¹ * ∑ r ∈ Finset.range (m + 2),
          (Nat.stirlingFirst (m + 1) r : ℝ) * (-1) ^ (m + 1 - r) *
            generalizedHarmonic (α - r) n

/-- **Gamma representation of the Stirling combination of generalized harmonic numbers.** Let
$s > 0$ be real and let $X_s$ be a random variable with the Gamma distribution
$\mathrm{Gamma}(s, 1)$ of shape $s$ and rate $1$. Write $[a, b]$ for the unsigned Stirling number
of the first kind, the number of permutations of $a$ elements with exactly $b$ cycles, and, for
real $t$ and a natural number $n$, write $H_n^{(t)} = \sum_{k=1}^{n} 1/k^t$ for the generalized
harmonic number. Then for all natural numbers $m$ and $n$,
$$\frac{1}{(m+1)!} \sum_{j=0}^{m+1} [m+1, j] (-1)^{m+1-j} H_n^{(s-j)} =
\sum_{k=0}^{n-1} \binom{k+1}{m+1} \mathbb{E}[e^{-k X_s}].$$

The source assumes $s > m + 1$; the identity holds for every $s > 0$.

Source: Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an
Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Corollary 1, Equation (8)
(`integers-2026-A124-cor-1`). -/
public theorem_wanted stirlingFirst_generalizedHarmonic_eq_gamma_expectation (m : ℕ) (s : ℝ)
    (hs : 0 < s) (n : ℕ) :
    ((m + 1).factorial : ℝ)⁻¹ * ∑ j ∈ Finset.range (m + 2),
        (Nat.stirlingFirst (m + 1) j : ℝ) * (-1) ^ (m + 1 - j) * generalizedHarmonic (s - j) n =
      ∑ k ∈ Finset.range n,
        ((k + 1).choose (m + 1) : ℝ) * ∫ x, Real.exp (-(k * x)) ∂gammaMeasure s 1

end

end MetaMathlibExt
