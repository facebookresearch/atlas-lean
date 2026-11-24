/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gamma
import Mathlib.Algebra.Field.GeomSum
import MathlibExt.Probability.Distributions.Gamma

/-!
# Generalized harmonic numbers and the Gamma distribution

For a real number `s` and a natural number `n`, the generalized harmonic number of order `s` is
`H_n^{(s)} = ∑_{k=1}^{n} 1 / k ^ s` (`MetaMathlibExt.generalizedHarmonic`). This file proves
Nakata's Gamma representation of these numbers: if `X_s` has the Gamma distribution of shape
`s > 0` and rate `1`, then
`H_n^{(s)} = ∑_{k=0}^{n-1} 𝔼[exp (-k X_s)] = 𝔼[(1 - exp (-n X_s)) / (1 - exp (-X_s))]`.

The first identity is the Laplace transform `𝔼[exp (-k X_s)] = 1 / (k + 1) ^ s` of the Gamma
distribution, summed over `k < n`. The second follows from the first and the geometric sum
`∑_{k=0}^{n-1} y ^ k = (1 - y ^ n) / (1 - y)` at `y = exp (-X_s)`, which applies almost surely
because `X_s > 0` almost surely.

## Main statements

* `MetaMathlibExt.generalizedHarmonic_eq_gamma_expectation`: the Gamma representation.

## References

* Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an Identity
  for Their Sums*, INTEGERS 26 (2026), Article A124, Lemma 1.
-/

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

namespace generalizedHarmonic_eq_gamma_expectation

/-- The generalized harmonic number $H_n^{(s)}$ as the sum of $1/(k+1)^s$ over $k < n$. -/
private theorem generalizedHarmonic_eq_sum_range (s : ℝ) (n : ℕ) :
    generalizedHarmonic s n = ∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ) ^ s)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih => rw [generalizedHarmonic_succ, ih, Finset.sum_range_succ]

/-- For $s > 0$ and a natural number $k$, the function $x \mapsto e^{-kx}$ is integrable for the
Gamma distribution of shape $s$ and rate $1$. -/
private theorem integrable_exp_neg_mul {s : ℝ} (hs : 0 < s) (k : ℕ) :
    Integrable (fun x : ℝ => Real.exp (-(k * x))) (gammaMeasure s 1) := by
  simpa using integrable_pow_mul_exp_neg_mul_gammaMeasure hs one_pos
    (by positivity : (0 : ℝ) < 1 + k) 0

/-- **Laplace transform of the Gamma distribution at a natural number.** If $X_s$ has the Gamma
distribution of shape $s > 0$ and rate $1$, then $\mathbb{E}[e^{-k X_s}] = 1/(k+1)^s$ for every
natural number $k$. -/
private theorem integral_exp_neg_mul {s : ℝ} (hs : 0 < s) (k : ℕ) :
    ∫ x, Real.exp (-(k * x)) ∂gammaMeasure s 1 = (((k + 1 : ℕ) : ℝ) ^ s)⁻¹ := by
  have h := integral_pow_mul_exp_neg_mul_gammaMeasure hs one_pos
    (by positivity : (0 : ℝ) < 1 + k) 0
  simp only [pow_zero, one_mul, ascPochhammer_zero, Polynomial.eval_one, Real.one_rpow,
    Nat.cast_zero, add_zero] at h
  rw [h, Nat.cast_add_one, add_comm, one_div]

/-- A random variable with the Gamma distribution of rate $1$ is almost surely positive. -/
private theorem ae_pos (s : ℝ) : ∀ᵐ x ∂gammaMeasure s 1, 0 < x := by
  have hne : ∀ᵐ x ∂gammaMeasure s 1, x ≠ 0 :=
    (withDensity_absolutelyContinuous _ _).ae_le (Measure.ae_ne volume 0)
  filter_upwards [ae_nonneg_gammaMeasure s 1, hne] with x hx hx0
  exact lt_of_le_of_ne hx (Ne.symm hx0)

/-- **Geometric sum of exponentials.** For real $x \ne 0$ and every natural number $n$,
$\sum_{k=0}^{n-1} e^{-kx} = (1 - e^{-nx}) / (1 - e^{-x})$. -/
private theorem sum_range_exp_neg_mul {x : ℝ} (hx : x ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.range n, Real.exp (-(k * x)) =
      (1 - Real.exp (-(n * x))) / (1 - Real.exp (-x)) := by
  have hexp (m : ℕ) : Real.exp (-(m * x)) = Real.exp (-x) ^ m := by
    rw [← Real.exp_nat_mul, mul_neg]
  have h1 : Real.exp (-x) ≠ 1 := by
    rw [Ne, Real.exp_eq_one_iff, neg_eq_zero]
    exact hx
  simp_rw [hexp]
  rw [geom_sum_eq h1, ← neg_div_neg_eq, neg_sub, neg_sub]

end generalizedHarmonic_eq_gamma_expectation

/-- **Gamma representation of generalized harmonic numbers.** Let $s > 0$ be real, let
$H_n^{(s)} = \sum_{k=1}^{n} 1/k^s$ denote the generalized harmonic numbers, and let $X_s$ be a
random variable with the Gamma distribution $\mathrm{Gamma}(s, 1)$ of shape $s$ and rate $1$. Then
for every natural number $n$,
$$H_n^{(s)} = \sum_{k=0}^{n-1} \mathbb{E}[e^{-k X_s}] =
\mathbb{E}\left[\frac{1 - e^{-n X_s}}{1 - e^{-X_s}}\right].$$

Source: Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an
Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Lemma 1, Equation (5)
(`integers-2026-A124-lem-1`). -/
theorem generalizedHarmonic_eq_gamma_expectation (s : ℝ) (hs : 0 < s) (n : ℕ) :
    generalizedHarmonic s n =
        ∑ k ∈ Finset.range n, ∫ x, Real.exp (-(k * x)) ∂gammaMeasure s 1 ∧
      generalizedHarmonic s n =
        ∫ x, (1 - Real.exp (-(n * x))) / (1 - Real.exp (-x)) ∂gammaMeasure s 1 := by
  have h₁ : generalizedHarmonic s n =
      ∑ k ∈ Finset.range n, ∫ x, Real.exp (-(k * x)) ∂gammaMeasure s 1 := by
    rw [generalizedHarmonic_eq_gamma_expectation.generalizedHarmonic_eq_sum_range]
    exact Finset.sum_congr rfl fun k _ =>
      (generalizedHarmonic_eq_gamma_expectation.integral_exp_neg_mul hs k).symm
  refine ⟨h₁, ?_⟩
  rw [h₁, ← integral_finsetSum _ fun k _ =>
    generalizedHarmonic_eq_gamma_expectation.integrable_exp_neg_mul hs k]
  refine integral_congr_ae ?_
  filter_upwards [generalizedHarmonic_eq_gamma_expectation.ae_pos s] with x hx
  exact generalizedHarmonic_eq_gamma_expectation.sum_range_exp_neg_mul hx.ne' n

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
theorem generalizedHarmonic_sub_eq_gamma_expectation (s : ℝ) (hs : 0 < s) (u : ℝ)
    (n : ℕ) :
    generalizedHarmonic (s - u) n =
      ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) ^ u * ∫ x, Real.exp (-(k * x)) ∂gammaMeasure s 1 := by
  rw [generalizedHarmonic_eq_gamma_expectation.generalizedHarmonic_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [generalizedHarmonic_eq_gamma_expectation.integral_exp_neg_mul hs,
    Real.rpow_sub (by positivity), inv_div, div_eq_mul_inv]

end

end MetaMathlibExt
