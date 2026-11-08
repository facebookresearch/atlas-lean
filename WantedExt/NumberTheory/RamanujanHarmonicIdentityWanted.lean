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

/-- **Corollary 1**: for `2 ≤ k ≤ n`, the shifted
binomial-harmonic convolution with upper summation limit `n + 1`.

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

/-- **Corollary 2**: for `1 ≤ k ≤ n - 1`, the companion shifted
binomial-harmonic convolution.

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

/-- **Lemma 1**: Ramanujan's generalized-binomial sine series.
For real `a`, `N ≥ 0`, and `|θ| ≤ π / 2`, the series
`∑' ν, (N choose ν) * sin((a + 2ν)θ)` converges to
`2^N * cos(θ)^N * sin((a + N)θ)`, with real powers.

Source: Horst Alzer and Man Kam Kwong, "Ramanujan and a
Combinatorial Identity Involving Harmonic Numbers",
Lemma 1. -/
theorem_wanted hasSum_ringChoose_mul_sin
    (a N θ : ℝ) (hN : 0 ≤ N) (hθ : |θ| ≤ Real.pi / 2) :
    HasSum
      (fun ν : ℕ => Ring.choose N ν * Real.sin ((a + 2 * (ν : ℝ)) * θ))
      ((2 : ℝ) ^ N * (Real.cos θ) ^ N * Real.sin ((a + N) * θ))

/-- **Lemma 3**: the Rung-Obaid finite trigonometric identity used
in the trigonometric proof of Theorem 1.

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

/-- **Lemma 4**: Gould's reciprocal generalized-binomial identity.
For real `x` different from `0, 1, …, N`,
`∑_{ν=0}^{N} (-1)^ν / (x - ν) * (N choose ν)` equals
`(-1)^N / ((x - N) * (x choose N))`.

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

/-- **Theorem 8**: uniqueness of the harmonic sequence for the
diagonal case `k = n - 1` of Theorem 1.  If a complex sequence `K`
satisfies the displayed identity for every `n ≥ 2`, then `K` is a
constant complex multiple of the harmonic numbers.

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
