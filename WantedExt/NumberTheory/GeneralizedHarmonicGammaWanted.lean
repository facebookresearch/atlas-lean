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

namespace MetaMathlibExt

@[expose] public section

open MeasureTheory ProbabilityTheory

/-- **Generalized harmonic numbers.** For a real number $s$ and a natural number $n$, the
generalized harmonic number of order $s$ is $H_n^{(s)} = \sum_{k=1}^{n} 1/k^s$, where $k^s$ is the
real power.

Source: Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an
Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Section 1 (definition of
`H_n^{(s)}`). -/
noncomputable def generalizedHarmonic (s : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, ((k : ℝ) ^ s)⁻¹

/-- **The zeroth generalized harmonic number.** For every real $s$, the generalized harmonic
number $H_n^{(s)} = \sum_{k=1}^{n} 1/k^s$ vanishes at $n = 0$: $H_0^{(s)} = 0$.

Source: Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an
Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Section 1 (definition of
`H_n^{(s)}`). -/
@[simp]
theorem generalizedHarmonic_zero (s : ℝ) : generalizedHarmonic s 0 = 0 := by
  simp [generalizedHarmonic]

/-- **Recurrence for generalized harmonic numbers.** For every real $s$ and every natural number
$n$, the generalized harmonic numbers $H_n^{(s)} = \sum_{k=1}^{n} 1/k^s$ satisfy
$H_{n+1}^{(s)} = H_n^{(s)} + 1/(n+1)^s$.

Source: Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an
Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Section 1 (definition of
`H_n^{(s)}`). -/
theorem generalizedHarmonic_succ (s : ℝ) (n : ℕ) :
    generalizedHarmonic s (n + 1) = generalizedHarmonic s n + (((n + 1 : ℕ) : ℝ) ^ s)⁻¹ := by
  simp [generalizedHarmonic, Finset.sum_Icc_succ_top (Nat.le_add_left 1 n)]

/-- **Gamma representation of generalized harmonic numbers.** Let $s > 0$ be real, let
$H_n^{(s)} = \sum_{k=1}^{n} 1/k^s$ denote the generalized harmonic numbers, and let $X_s$ be a
random variable with the Gamma distribution $\mathrm{Gamma}(s, 1)$ of shape $s$ and rate $1$. Then
for every natural number $n$,
$$H_n^{(s)} = \sum_{k=0}^{n-1} \mathbb{E}[e^{-k X_s}] =
\mathbb{E}\left[\frac{1 - e^{-n X_s}}{1 - e^{-X_s}}\right].$$

Source: Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an
Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Lemma 1, Equation (5)
(`integers-2026-A124-lem-1`). -/
public theorem_wanted generalizedHarmonic_eq_gamma_expectation (s : ℝ) (hs : 0 < s) (n : ℕ) :
    generalizedHarmonic s n =
        ∑ k ∈ Finset.range n, ∫ x, Real.exp (-(k * x)) ∂gammaMeasure s 1 ∧
      generalizedHarmonic s n =
        ∫ x, (1 - Real.exp (-(n * x))) / (1 - Real.exp (-x)) ∂gammaMeasure s 1

/-- **Shifted Gamma representation of generalized harmonic numbers.** For real $t$ and a natural
number $n$, write $H_n^{(t)} = \sum_{k=1}^{n} 1/k^t$ for the generalized harmonic number. Let
$s > 0$ be real and let $X_s$ be a random variable with the Gamma distribution
$\mathrm{Gamma}(s, 1)$ of shape $s$ and rate $1$. Then for every real $u$ and every natural
number $n$,
$$H_n^{(s-u)} = \sum_{k=0}^{n-1} (k+1)^u \, \mathbb{E}[e^{-k X_s}].$$

The source assumes $0 < u < s$; the identity holds for every real $u$.

Source: Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an
Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Lemma 2, Equation (7)
(`integers-2026-A124-lem-2`). -/
public theorem_wanted generalizedHarmonic_sub_eq_gamma_expectation (s : ℝ) (hs : 0 < s) (u : ℝ)
    (n : ℕ) :
    generalizedHarmonic (s - u) n =
      ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) ^ u * ∫ x, Real.exp (-(k * x)) ∂gammaMeasure s 1

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
