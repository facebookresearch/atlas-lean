/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ramanujan and a combinatorial identity involving harmonic numbers

Remaining statements from Horst Alzer and Man Kam Kwong,
"Ramanujan and a Combinatorial Identity Involving Harmonic Numbers",
*Journal of Integer Sequences* 29 (2026), Article 26.4.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Alzer/alzer22.html>).
The publisher TeX at
<https://cs.uwaterloo.ca/journals/JIS/VOL29/Alzer/alzer22.tex>
is the source used for the formulas below.

Three records from this paper are already proved in MathlibExt and
are not restated here: Theorem 1 is
`MathlibExt.NumberTheory.binomial_harmonic_convolution`; Lemma 2
is the third conjunct of
`MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry33Zeta3integral.ramanujan_part1_ch9_entry33_zeta3integral_general`
(after unfolding `chapter9Entry33WeightedIntegrand`, and stronger:
it also proves integrability and holds at `n = 0`); and the final
theorem that `∑_{ν=2}^{n} H_ν` is not an integer is
`MathlibExt.NumberTheory.harmonic_partial_sum_not_int`.

Generalized binomial coefficients of a real top are Mathlib's
`Ring.choose`.  The infinite series in Lemma 1 is stated with
`HasSum`, so it asserts convergence to the displayed value rather
than only an equality of `tsum` terms.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.RingTheory.Binomial
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted

/-- **Shifted binomial–harmonic convolution (Alzer–Kwong, Corollary 1).** For natural numbers $k$
and $n$ with $2 \le k \le n$,
$$
\sum_{\nu=1}^{n+1} \Bigl(\binom{n+k-\nu-1}{n} - \binom{n+k-\nu-1}{k-2}\Bigr) H_\nu =
\binom{n+k}{k-1} (H_k - H_{n+1}) - \frac{1}{n+1} \binom{n+k}{k},
$$
where $H_m = \sum_{j=1}^{m} 1/j$ is the $m$-th harmonic number.

Source: Horst Alzer and Man Kam Kwong, "Ramanujan and a
Combinatorial Identity Involving Harmonic Numbers",
Corollary 1. -/
theorem_wanted sum_choose_sub_choose_mul_harmonic_succ_eq
    (k n : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    ∑ ν ∈ Finset.Icc 1 (n + 1),
        ((Nat.choose (n + k - ν - 1) n : ℚ) -
          (Nat.choose (n + k - ν - 1) (k - 2) : ℚ)) * harmonic ν =
      (Nat.choose (n + k) (k - 1) : ℚ) *
          (harmonic k - harmonic (n + 1)) -
        (1 / ((n : ℚ) + 1)) * (Nat.choose (n + k) k : ℚ)

/-- **Shifted binomial–harmonic convolution (Alzer–Kwong, Corollary 2).** For natural numbers $k$
and $n$ with $1 \le k \le n - 1$,
$$
\sum_{\nu=1}^{n} \Bigl(\binom{n+k-\nu-1}{n-2} - \binom{n+k-\nu-1}{k}\Bigr) H_\nu =
\binom{n+k}{k+1} (H_k - H_n) + \frac{1}{k+1} \binom{n+k+1}{k+1},
$$
where $H_m = \sum_{j=1}^{m} 1/j$ is the $m$-th harmonic number.

Source: Horst Alzer and Man Kam Kwong, "Ramanujan and a
Combinatorial Identity Involving Harmonic Numbers",
Corollary 2. -/
theorem_wanted sum_choose_sub_choose_mul_harmonic_eq_add
    (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n - 1) :
    ∑ ν ∈ Finset.Icc 1 n,
        ((Nat.choose (n + k - ν - 1) (n - 2) : ℚ) -
          (Nat.choose (n + k - ν - 1) k : ℚ)) * harmonic ν =
      (Nat.choose (n + k) (k + 1) : ℚ) * (harmonic k - harmonic n) +
        (1 / ((k : ℚ) + 1)) * (Nat.choose (n + k + 1) (k + 1) : ℚ)

/-- **Ramanujan's binomial sine series.** Let $a$, $N$ and $\theta$ be real numbers with
$N \ge 0$ and $|\theta| \le \pi / 2$. Then the series
$\sum_{\nu=0}^{\infty} \binom{N}{\nu} \sin((a + 2\nu)\theta)$ converges unconditionally to
$2^N (\cos \theta)^N \sin((a + N)\theta)$. Here $\binom{N}{\nu} = N(N-1)\cdots(N-\nu+1)/\nu!$
is the generalized binomial coefficient, and $2^N$ and $(\cos \theta)^N$ are real powers.

Source: Horst Alzer and Man Kam Kwong, "Ramanujan and a
Combinatorial Identity Involving Harmonic Numbers",
Lemma 1. -/
theorem_wanted hasSum_ringChoose_mul_sin
    (a N θ : ℝ) (hN : 0 ≤ N) (hθ : |θ| ≤ Real.pi / 2) :
    HasSum
      (fun ν : ℕ => Ring.choose N ν * Real.sin ((a + 2 * (ν : ℝ)) * θ))
      ((2 : ℝ) ^ N * (Real.cos θ) ^ N * Real.sin ((a + N) * θ))

/-- **The Rung-Obaid trigonometric identity.** Let $k$ and $n$ be natural numbers with
$1 \le k \le n$, and let $\theta$ be a real number. Then

$$\sum_{\nu=1}^{n} 2^\nu \left( \binom{n+k-\nu-1}{k-1} - \binom{n+k-\nu-1}{n-1} \right)
\cos^\nu \theta \, \sin(\nu\theta) = 2^{n+k} \cos^{n+k} \theta \, \sin((n-k)\theta).$$

Source: Horst Alzer and Man Kam Kwong, "Ramanujan and a
Combinatorial Identity Involving Harmonic Numbers",
Lemma 3. -/
theorem_wanted sum_two_pow_choose_sub_mul_cos_pow_sin
    (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (θ : ℝ) :
    ∑ ν ∈ Finset.Icc 1 n,
        (2 : ℝ) ^ ν *
          ((Nat.choose (n + k - ν - 1) (k - 1) : ℝ) -
            (Nat.choose (n + k - ν - 1) (n - 1) : ℝ)) *
          Real.cos θ ^ ν * Real.sin ((ν : ℝ) * θ) =
      (2 : ℝ) ^ (n + k) * Real.cos θ ^ (n + k) *
        Real.sin (((n : ℝ) - (k : ℝ)) * θ)

/-- **Gould's reciprocal binomial identity (Alzer–Kwong, Lemma 4).** Let $N$ be a natural number
and $x$ a real number with $x \ne \nu$ for every $\nu \in \{0, 1, \dots, N\}$. Then
$$
\sum_{\nu=0}^{N} \frac{(-1)^\nu}{x - \nu} \binom{N}{\nu} = \frac{(-1)^N}{(x - N) \binom{x}{N}},
$$
where $\binom{x}{N} = x(x-1)\cdots(x-N+1)/N!$ is the generalized binomial coefficient.

Source: Horst Alzer and Man Kam Kwong, "Ramanujan and a
Combinatorial Identity Involving Harmonic Numbers",
Lemma 4. -/
theorem_wanted sum_neg_one_pow_div_mul_choose_eq
    (N : ℕ) (x : ℝ)
    (hx : ∀ ν ∈ Finset.Icc 0 N, x ≠ (ν : ℝ)) :
    ∑ ν ∈ Finset.Icc 0 N,
        ((-1 : ℝ) ^ ν / (x - (ν : ℝ))) *
          (Nat.choose N ν : ℝ) =
      (-1 : ℝ) ^ N / ((x - (N : ℝ)) * Ring.choose x N)

/-- **Uniqueness of the harmonic solution of the diagonal Ramanujan identity.** Let
$K : \mathbb{N} \to \mathbb{C}$ be a sequence such that for every integer $n \ge 2$
$$
\sum_{\nu=2}^{n} \Bigl(\binom{2n-\nu-2}{n-1} - \binom{2n-\nu-2}{n-2}\Bigr) K(\nu) =
\binom{2n-1}{n-1} \bigl(K(n-1) - K(n)\bigr).
$$
Then there is a constant $\lambda \in \mathbb{C}$ such that $K(r) = \lambda H_r$ for every integer
$r \ge 1$, where $H_r = \sum_{j=1}^{r} 1/j$ is the $r$-th harmonic number.

Source: Horst Alzer and Man Kam Kwong, "Ramanujan and a
Combinatorial Identity Involving Harmonic Numbers",
Theorem 8. -/
theorem_wanted eq_lambda_mul_harmonic_of_sum_choose_sub_mul_eq
    (K : ℕ → ℂ)
    (hK : ∀ n : ℕ, 2 ≤ n →
      ∑ ν ∈ Finset.Icc 2 n,
          (((Nat.choose (2 * n - ν - 2) (n - 1) : ℂ) -
            (Nat.choose (2 * n - ν - 2) (n - 2) : ℂ)) * K ν) =
        (Nat.choose (2 * n - 1) (n - 1) : ℂ) * (K (n - 1) - K n)) :
    ∃ lam : ℂ, ∀ r : ℕ, 1 ≤ r → K r = lam * (harmonic r : ℂ)

end MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted
