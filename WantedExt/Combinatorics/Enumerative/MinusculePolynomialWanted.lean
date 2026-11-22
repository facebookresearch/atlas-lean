/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real
public import MathlibExt.Algebra.Polynomial.RealRooted
public import MathlibExt.LinearAlgebra.Matrix.NonnegativeMinors

/-!
# Minuscule polynomials of type A

Statements from Ming-Jian Ding and Jiang Zeng, *Some New Results on the Minuscule Polynomials
of Type A*, Journal of Integer Sequences 28 (2025), Article 25.1.2
(arXiv:2308.16782v3, which carries the same definition (1.1) and results).
-/

namespace MetaMathlibExt

open Polynomial Filter Topology

@[expose] public section

/-- The type-A minuscule polynomial
`N_n(x) = (1 / (4n + 2)) ∑_{k=1}^{n-1} k (n - k) binom(2n + 2, 2k + 1) x^k`.
For `n = 0` the sum is empty, so `N_0 = 0`.

Source: Ming-Jian Ding and Jiang Zeng, *Some New Results on the Minuscule Polynomials of
Type A*, Journal of Integer Sequences 28 (2025), Article 25.1.2, definition (1.1)
(arXiv:2308.16782v3, equation (1.1)). -/
public noncomputable def minusculePolynomialA (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.Icc 1 (n - 1),
    C ((k : ℚ) * ((n : ℚ) - k) * ((2 * n + 2).choose (2 * k + 1) : ℚ) / (4 * n + 2)) * X ^ k

/-- `N_1 = 0`.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, table of `N_n(x)` after (1.1). -/
public theorem minusculePolynomialA_one : minusculePolynomialA 1 = 0 := by
  simp [minusculePolynomialA]

/-- `N_2(x) = 2x`.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, table of `N_n(x)` after (1.1). -/
public theorem minusculePolynomialA_two : minusculePolynomialA 2 = C 2 * X := by
  simp [minusculePolynomialA, Nat.choose]
  norm_num

/-- `N_3(x) = 8x + 8x^2`.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, table of `N_n(x)` after (1.1). -/
public theorem minusculePolynomialA_three :
    minusculePolynomialA 3 = C 8 * X + C 8 * X ^ 2 := by
  rw [minusculePolynomialA, show Finset.Icc 1 (3 - 1) = {1, 2} by decide]
  simp [Nat.choose]
  norm_num

/-- Real-rootedness: every complex root of `N_n(x)` is real. Stated for every `n : ℕ`; the paper
says positive `n`, and `N_0 = 0` has no roots.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Theorem 5 (first part). -/
public theorem_wanted minusculePolynomialA_isRealRooted (n : ℕ) :
    ((minusculePolynomialA n).map (algebraMap ℚ ℂ)).IsRealRooted

/-- Interlacing `N_n ⪯ N_{n+1}`: for `n ≥ 2`, `N_{n+1}` (degree `n`) and `N_n` (degree `n - 1`)
factor over `ℝ` with real roots `r_0 ≤ ⋯ ≤ r_{n-1}` and `s_0 ≤ ⋯ ≤ s_{n-2}` such that
`r_j ≤ s_j ≤ r_{j+1}`, which is relation (1.2) of the paper written in increasing order.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Theorem 5 (second part). -/
public theorem_wanted minusculePolynomialA_interlaces_succ (n : ℕ) (hn : 2 ≤ n) :
    ∃ (c d : ℝ) (r : Fin n → ℝ) (s : Fin (n - 1) → ℝ), c ≠ 0 ∧ d ≠ 0 ∧
      Monotone r ∧ Monotone s ∧
      (minusculePolynomialA (n + 1)).map (algebraMap ℚ ℝ) = C c * ∏ i, (X - C (r i)) ∧
      (minusculePolynomialA n).map (algebraMap ℚ ℝ) = C d * ∏ j, (X - C (s j)) ∧
      ∀ (j : ℕ) (hj : j + 1 < n),
        r ⟨j, by omega⟩ ≤ s ⟨j, by omega⟩ ∧ s ⟨j, by omega⟩ ≤ r ⟨j + 1, hj⟩

/-- The coefficients of `N_n(x)` are log-concave: `N_{n,k-1} N_{n,k+1} ≤ N_{n,k}^2`. Stated for
all `n, k : ℕ`; the cases outside `n ≥ 1`, `1 ≤ k ≤ n - 1` hold because the extra coefficients
vanish.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Corollary 7. -/
public theorem_wanted minusculePolynomialA_coeff_logConcave (n k : ℕ) :
    (minusculePolynomialA n).coeff (k - 1) * (minusculePolynomialA n).coeff (k + 1) ≤
      (minusculePolynomialA n).coeff k ^ 2

/-- Gamma-positivity: `N_n(x) = ∑_{k=0}^{⌊n/2⌋} γ_{n,k} x^k (1 + x)^{n-2k}` with non-negative
integers `γ_{n,k}`. Stated for every `n : ℕ` (`N_0 = 0`).

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Corollary 8. -/
public theorem_wanted minusculePolynomialA_gamma_positive (n : ℕ) :
    ∃ γ : ℕ → ℕ, minusculePolynomialA n =
      ∑ k ∈ Finset.range (n / 2 + 1), C (γ k : ℚ) * X ^ k * (1 + X) ^ (n - 2 * k)

/-- The identity
`N_n(x^2) = (n+1)/8 ((1+x)^{2n} + (1-x)^{2n}) - 1/(16x) ((1+x)^{2n+2} - (1-x)^{2n+2})`,
multiplied through by `16x` to stay in `ℚ[X]`. Stated for every `n : ℕ` (both sides vanish
at `n = 0`).

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Proposition 9. -/
public theorem_wanted minusculePolynomialA_comp_sq (n : ℕ) :
    C 16 * X * (minusculePolynomialA n).comp (X ^ 2) =
      C (2 * ((n : ℚ) + 1)) * X * ((1 + X) ^ (2 * n) + (1 - X) ^ (2 * n)) -
        ((1 + X) ^ (2 * n + 2) - (1 - X) ^ (2 * n + 2))

/-- Exponential generating function: for real `x ≠ 0` and real `z`,
`∑ N_n(x^2) z^n / n! = (2x(1+x)^2 z - 1 - x^2)/(16x) e^{(1+x)^2 z}
+ (2x(1-x)^2 z + 1 + x^2)/(16x) e^{(1-x)^2 z}`. The sum starts at `n = 0`, where `N_0 = 0`.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Proposition 10. -/
public theorem_wanted minusculePolynomialA_egf (x z : ℝ) (hx : x ≠ 0) :
    HasSum (fun n : ℕ => aeval (x ^ 2) (minusculePolynomialA n) * z ^ n / n.factorial)
      ((2 * x * (1 + x) ^ 2 * z - 1 - x ^ 2) / (16 * x) * Real.exp ((1 + x) ^ 2 * z) +
        (2 * x * (1 - x) ^ 2 * z + 1 + x ^ 2) / (16 * x) * Real.exp ((1 - x) ^ 2 * z))

/-- `N_n(1) = (n - 1) 2^{2n-3}` for positive `n` (Bourn–Erickson conjecture).

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Corollary 11. -/
public theorem_wanted minusculePolynomialA_eval_one (n : ℕ) (hn : 1 ≤ n) :
    (minusculePolynomialA n).eval 1 = ((n : ℚ) - 1) * 2 ^ ((2 * n : ℤ) - 3)

/-- Bender's criterion. Let `A_n(x) = ∏_{i<n} (x + r_{n,i})` with all `r_{n,i} ≥ 0` (a monic
degree-`n` polynomial whose zeros `-r_{n,i}` are real and non-positive), with coefficients
`a(n,k)`. Then the normalized coefficient distribution has mean `μ_n = ∑ 1/(1 + r_{n,i})` and
variance `σ_n^2 = ∑ r_{n,i}/(1 + r_{n,i})^2`, and if `σ_n → ∞` it is asymptotically normal:
for every real `x`, `∑_{k ≤ μ_n + x σ_n} a(n,k) / ∑_k a(n,k)` tends to the standard normal
distribution function at `x`.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Lemma 12 (Bender, Theorem 2). -/
public theorem_wanted bender_asymptotic_normality (r : (n : ℕ) → Fin n → ℝ)
    (hr : ∀ n i, 0 ≤ r n i) :
    let a : ℕ → ℕ → ℝ := fun n k => (∏ i, (X + C (r n i))).coeff k
    let μ : ℕ → ℝ := fun n => ∑ i, 1 / (1 + r n i)
    let σ2 : ℕ → ℝ := fun n => ∑ i, r n i / (1 + r n i) ^ 2
    (∀ n, (∑ k ∈ Finset.range (n + 1), (k : ℝ) * a n k) /
          (∑ k ∈ Finset.range (n + 1), a n k) = μ n ∧
        (∑ k ∈ Finset.range (n + 1), ((k : ℝ) - μ n) ^ 2 * a n k) /
          (∑ k ∈ Finset.range (n + 1), a n k) = σ2 n) ∧
    (Tendsto σ2 atTop atTop → ∀ x : ℝ,
      Tendsto (fun n => (∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ μ n + x * √(σ2 n)),
            a n k) /
          (∑ k ∈ Finset.range (n + 1), a n k))
        atTop (𝓝 (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x)))

/-- The coefficients of `N_n(x)` are asymptotically normal with mean `n/2` and variance
`(n^2 - n - 2)/(8(n - 1))`: for every real `x`,
`∑_{k ≤ n/2 + x σ_n} N_{n,k} / N_n(1)` tends to the standard normal distribution function.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Theorem 13. -/
public theorem_wanted minusculePolynomialA_asymptotically_normal (x : ℝ) :
    Tendsto (fun n : ℕ =>
        (∑ k ∈ (Finset.range n).filter (fun k : ℕ =>
            (k : ℝ) ≤ n / 2 + x * √(((n : ℝ) ^ 2 - n - 2) / (8 * ((n : ℝ) - 1)))),
          ((minusculePolynomialA n).coeff k : ℝ)) / (((minusculePolynomialA n).eval 1 : ℚ) : ℝ))
      atTop (𝓝 (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x))

/-- `x`-log-concavity: every coefficient of `N_n(x)^2 - N_{n+1}(x) N_{n-1}(x)` is
non-negative. Stated for every `n : ℕ`; for `n ≤ 1` the polynomial is `0` since
`N_0 = N_1 = 0`.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Theorem 14. -/
public theorem_wanted minusculePolynomialA_x_logConcave (n k : ℕ) :
    0 ≤ (minusculePolynomialA n ^ 2 -
      minusculePolynomialA (n + 1) * minusculePolynomialA (n - 1)).coeff k

/-- The coefficient matrix `[N_{n,k}]_{n,k ≥ 1}` (zero above the diagonal) is totally positive:
all its minors are non-negative. Row `i` and column `j` hold `N_{i+1, j+1}`.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Theorem 19. -/
public theorem_wanted minusculePolynomialA_coeffMatrix_hasNonnegativeMinors :
    Matrix.HasNonnegativeMinors
      (Matrix.of fun i j : ℕ => ((minusculePolynomialA (i + 1)).coeff (j + 1) : ℝ))

/-- Craven–Csordas: a finite real sequence `(t_k)_{k=0}^n` is a multiplier `n`-sequence (it maps
every real-rooted real polynomial of degree at most `n`, `∑ a_k x^k`, to a real-rooted one,
`∑ a_k t_k x^k`) if and only if `∑_{k=0}^n binom(n,k) t_k x^k` is real-rooted with all zeros of
the same (weak) sign. Only `t 0, …, t n` matter.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Lemma 3 (Craven and Csordas, Theorem 3.7). -/
public theorem_wanted multiplier_n_sequence_iff (n : ℕ) (t : ℕ → ℝ) :
    (∀ p : ℝ[X], p.natDegree ≤ n → p.Splits →
      (∑ k ∈ Finset.range (n + 1), C (p.coeff k * t k) * X ^ k).Splits) ↔
    ((∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℝ) * t k) * X ^ k).Splits ∧
      ((∀ x ∈ (∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℝ) * t k) * X ^ k).roots, 0 ≤ x) ∨
        ∀ x ∈ (∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℝ) * t k) * X ^ k).roots, x ≤ 0))

/-- Pólya–Schur: a non-negative sequence `(t_k)_{k ≥ 0}` is a multiplier sequence (it maps every
real-rooted real polynomial `∑ a_k x^k` to a real-rooted `∑ a_k t_k x^k`) if and only if, for
each `n ≥ 1`, `∑_{k=0}^n binom(n,k) t_k x^k` is real-rooted with all zeros of the same (weak)
sign.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Lemma 18 (Pólya and Schur). -/
public theorem_wanted multiplier_sequence_iff (t : ℕ → ℝ) (ht : ∀ k, 0 ≤ t k) :
    (∀ p : ℝ[X], p.Splits →
      (∑ k ∈ Finset.range (p.natDegree + 1), C (p.coeff k * t k) * X ^ k).Splits) ↔
    ∀ n, 1 ≤ n →
      (∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℝ) * t k) * X ^ k).Splits ∧
        ((∀ x ∈ (∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℝ) * t k) * X ^ k).roots,
            0 ≤ x) ∨
          ∀ x ∈ (∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℝ) * t k) * X ^ k).roots, x ≤ 0)

/-- Aissen–Schoenberg–Whitney–Edrei: a non-negative sequence `(a_n)` with `a_0 ≠ 0` is a Pólya
frequency sequence (its Toeplitz matrix `[a_{n-k}]_{n,k ≥ 0}`, zero above the diagonal, is
totally positive) if and only if its ordinary generating function has the form
`a_0 e^{γx} ∏ (1 + α_i x) / ∏ (1 - β_i x)` with `α_i, β_i, γ ≥ 0` and `∑ (α_i + β_i) < ∞`.
The generating-function identity is read near `0`: the power series converges to that product
on some interval `|x| < ε`.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Lemma 16 (Schoenberg–Edrei Theorem, Karlin p. 154). -/
public theorem_wanted polyaFrequency_iff_hasSum_edrei_product (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (ha0 : a 0 ≠ 0) :
    Matrix.HasNonnegativeMinors (Matrix.of fun n k : ℕ => if k ≤ n then a (n - k) else 0) ↔
      ∃ (γ : ℝ) (α β : ℕ → ℝ), 0 ≤ γ ∧ (∀ i, 0 ≤ α i) ∧ (∀ i, 0 ≤ β i) ∧
        Summable (fun i => α i + β i) ∧ ∃ ε > 0, ∀ x : ℝ, |x| < ε →
          HasSum (fun n => a n * x ^ n)
            (a 0 * Real.exp (γ * x) * (∏' i, (1 + α i * x)) / ∏' i, (1 - β i * x))

/-- Pólya–Schur, transcendental characterization: a non-negative sequence `(λ_n)` with
`λ_0 ≠ 0` is a multiplier sequence (it maps every real-rooted real polynomial `∑ a_k x^k` to a
real-rooted `∑ a_k λ_k x^k`) if and only if its exponential generating function is the real
entire function `λ_0 e^{γx} ∏ (1 + α_i x)` with `γ ≥ 0`, `α_i ≥ 0` and `∑ α_i < ∞`; "entire"
is encoded as convergence of `∑ λ_n x^n / n!` to that product at every real `x`.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Lemma 17 (Pólya and Schur, PS14 p. 93). -/
public theorem_wanted multiplier_sequence_iff_hasSum_exp_mul_tprod (t : ℕ → ℝ)
    (ht : ∀ k, 0 ≤ t k) (ht0 : t 0 ≠ 0) :
    (∀ p : ℝ[X], p.Splits →
      (∑ k ∈ Finset.range (p.natDegree + 1), C (p.coeff k * t k) * X ^ k).Splits) ↔
      ∃ (γ : ℝ) (α : ℕ → ℝ), 0 ≤ γ ∧ (∀ i, 0 ≤ α i) ∧ Summable α ∧ ∀ x : ℝ,
        HasSum (fun n => t n / n.factorial * x ^ n)
          (t 0 * Real.exp (γ * x) * ∏' i, (1 + α i * x))

end

end MetaMathlibExt
