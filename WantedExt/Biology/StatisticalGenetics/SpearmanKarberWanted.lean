/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Spearman–Kärber estimator of the mean tolerance

In a quantal bioassay, doses on an equally spaced (log-)scale `xᵢ = x₀ + i d`, `i = 0, …, k`,
with spacing `d > 0`, are given to `n` subjects each; at dose `i` the true response probability is
`Pᵢ`, with `P₀ = 0` and `P_k = 1`, and the observed proportion is `p̂ᵢ = rᵢ / n` for a binomial
count `rᵢ`. The Spearman–Kärber estimator is
`m = ∑ᵢ (p̂ᵢ₊₁ - p̂ᵢ) (xᵢ + xᵢ₊₁) / 2`, which Irwin and Cheeseman (1939, p. 574) write as
`m = x_k - d (½ p̂₀ + p̂₁ + ⋯ + p̂_{k-1} + ½ p̂_k)`. With the true probabilities in place of the
proportions it is the mean of the interpolated tolerance distribution, which puts mass
`Pᵢ₊₁ - Pᵢ` at the midpoint `(xᵢ + xᵢ₊₁) / 2`; it is an unbiased estimator of that mean, with
variance `d² ∑ᵢ Pᵢ (1 - Pᵢ) / n` when the counts are independent (the standard error
`d √(∑ pq / n)` of Irwin and Cheeseman, p. 574).

Recorded here: the summation-by-parts form, unbiasedness for the interpolated mean, and the exact
variance, for independent binomial counts. Spearman (1908) and Kärber (1931) are attribution only;
the statement follows Irwin and Cheeseman (1939, pp. 574–580, read). Unbiasedness and exactness of
the variance are derived. The vague claim of unbiasedness "up to the discretization error" for a
continuous tolerance law is not formalized.

Sources: J. O. Irwin and E. A. Cheeseman, "On an approximate method of determining the median
effective dose and its error, in the case of a quantal response", J. Hyg. 39 (1939) 574–580,
doi:10.1017/S0022172400012213, p. 574; C. Spearman, "The method of 'right and wrong cases'
('constant stimuli') without Gauss's formulae", Brit. J. Psychol. 2 (1908) 227–242; G. Kärber,
Arch. Exp. Path. Pharmak. 162 (1931) 480–483.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.SpearmanKarberWanted

open Finset

/-- The Spearman–Kärber value `∑ᵢ (pᵢ₊₁ - pᵢ) (xᵢ + xᵢ₊₁) / 2` for doses `xᵢ = x₀ + i d`,
`i = 0, …, k`, and response proportions `p`; for nondecreasing `p` with `p₀ = 0` and `p_k = 1` it
is the mean of the distribution with mass `pᵢ₊₁ - pᵢ` at `(xᵢ + xᵢ₊₁) / 2`. -/
noncomputable def spearmanKarber (x₀ d : ℝ) {k : ℕ} (p : Fin (k + 1) → ℝ) : ℝ :=
  ∑ i : Fin k, (p i.succ - p i.castSucc) *
    ((x₀ + (i : ℕ) * d) + (x₀ + ((i : ℕ) + 1) * d)) / 2

/-- The binomial probability `C(n, r) Pʳ (1 - P)ⁿ⁻ʳ` of `r` responders among `n` subjects. -/
noncomputable def binomProb (n : ℕ) (P : ℝ) (r : Fin (n + 1)) : ℝ :=
  (n.choose r : ℝ) * P ^ (r : ℕ) * (1 - P) ^ (n - r)

/-- The expectation of a function of the response counts `r : Fin (k + 1) → Fin (n + 1)` when the
counts at the different doses are independent binomial(`n`, `Pᵢ`). -/
noncomputable def expect {k : ℕ} (n : ℕ) (P : Fin (k + 1) → ℝ)
    (f : (Fin (k + 1) → Fin (n + 1)) → ℝ) : ℝ :=
  ∑ r : Fin (k + 1) → Fin (n + 1), (∏ i, binomProb n (P i) (r i)) * f r

/-- The estimator computed from the counts: the Spearman–Kärber value of the proportions
`rᵢ / n`. -/
noncomputable def estimator (x₀ d : ℝ) {k : ℕ} (n : ℕ) (r : Fin (k + 1) → Fin (n + 1)) : ℝ :=
  spearmanKarber x₀ d (fun i => ((r i : ℕ) : ℝ) / n)

/-- **Summation by parts** (Irwin and Cheeseman 1939, p. 574): for doses `xᵢ = x₀ + i d`,
`i = 0, …, k` with `k ≥ 1`, and any proportions `p` with `p₀ = 0` and `p_k = 1`, the
Spearman–Kärber value equals `x_k - d (½ p₀ + p₁ + ⋯ + p_{k-1} + ½ p_k)`.

Source: Irwin and Cheeseman (1939), p. 574. -/
public theorem_wanted spearmanKarber_eq (x₀ d : ℝ) (k : ℕ) (hk : 1 ≤ k) (p : Fin (k + 1) → ℝ)
    (h₀ : p 0 = 0) (hk₁ : p (Fin.last k) = 1) :
    spearmanKarber x₀ d p =
      (x₀ + k * d) - d * (p 0 / 2 + ∑ i : Fin (k + 1), (if i = 0 ∨ i = Fin.last k then 0 else p i) +
        p (Fin.last k) / 2)

/-- **Unbiasedness and exact variance** (Irwin and Cheeseman 1939, p. 574; derived): let `d > 0`,
`n ≥ 1`, and let the true response probabilities satisfy `0 ≤ Pᵢ ≤ 1`, `P₀ = 0`, `P_k = 1`, and
be nondecreasing in dose (`Pᵢ ≤ Pᵢ₊₁` for `i < k`), so that the interpolated tolerance
distribution, with mass `Pᵢ₊₁ - Pᵢ ≥ 0` at `(xᵢ + xᵢ₊₁) / 2`, is a probability distribution.
For independent binomial(`n`, `Pᵢ`) counts at the doses `xᵢ = x₀ + i d`, the Spearman–Kärber
estimator `m` has expectation equal to the mean of the interpolated tolerance distribution,
`E[m] = ∑ᵢ (Pᵢ₊₁ - Pᵢ) (xᵢ + xᵢ₊₁) / 2`, and variance `E[(m - E[m])²] = d² ∑ᵢ Pᵢ (1 - Pᵢ) / n`.

Source: Irwin and Cheeseman (1939), p. 574. -/
public theorem_wanted expect_variance (x₀ d : ℝ) (hd : 0 < d) (k n : ℕ) (hn : 1 ≤ n)
    (P : Fin (k + 1) → ℝ) (hP : ∀ i, 0 ≤ P i ∧ P i ≤ 1) (h₀ : P 0 = 0)
    (hk₁ : P (Fin.last k) = 1) (hmono : ∀ i : Fin k, P i.castSucc ≤ P i.succ) :
    expect n P (estimator x₀ d n) = spearmanKarber x₀ d P ∧
      expect n P (fun r => (estimator x₀ d n r - spearmanKarber x₀ d P) ^ 2) =
        d ^ 2 * (∑ i, P i * (1 - P i)) / n

end WantedExt.Biology.StatisticalGenetics.SpearmanKarberWanted
