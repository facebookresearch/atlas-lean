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

The diagonal uniqueness theorem and Ramanujan's binomial sine series are proved in
`MathlibExt.NumberTheory.RamanujanHarmonicIdentity` and
`MathlibExt.NumberTheory.RamanujanBinomialSine`, respectively.
Three other records from this paper are already proved in MathlibExt and
are not restated here: Theorem 1 is
`MetaMathlibExt.binomial_harmonic_convolution`; Lemma 2
is the third conjunct of `ramanujan_part1_ch9_entry33_zeta3integral_general`
in the namespace `MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry33Zeta3integral`
(after unfolding `chapter9Entry33WeightedIntegrand`, and stronger:
it also proves integrability and holds at `n = 0`); and the final
theorem that `∑_{ν=2}^{n} H_ν` is not an integer is
`MetaMathlibExt.harmonic_partial_sum_not_int`.

Generalized binomial coefficients of a real top are Mathlib's `Ring.choose`.
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
public import MathlibExt.NumberTheory.GouldReciprocalBinomial
public import MathlibExt.NumberTheory.RamanujanBinomialSine
public import MathlibExt.NumberTheory.RamanujanHarmonicIdentity

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

end MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted
