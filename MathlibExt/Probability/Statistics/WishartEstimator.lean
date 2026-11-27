/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.WishartTrace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A moments estimator from the spectrum of a finite real Wishart matrix

For a sample `M`, put `X = M Mᵀ`, `s = tr X` and `t = tr(X²)`. No column centring or
normalisation is performed. For a natural number `n` of columns and independent centred
Gaussian entries of variance `v`, the means of `s` and `2t + s²` are `mnv` and
`m(m+2)n(n+2)v²`. Patterson, Price and Reich fit the two observed statistics by evaluating
these polynomials at a positive real count `r` and a candidate variance `u` in place of
`n` and `v`. This is a deterministic fit, not a Gaussian matrix law with `r` columns.
When `m t − s² > 0`, the fit is unique. This positive dispersion condition holds
almost surely for positive entry variance, at least two rows and at least one column; it
is not a claim about every sample from that law.

Source: N. Patterson, A. L. Price and D. Reich, “Population Structure and Eigenanalysis”,
PLOS Genetics 2 (2006), e190, Theorem 1 and equations (23)–(26), pp. 2089–2090,
<https://doi.org/10.1371/journal.pgen.0020190>.
-/

@[expose] public section

noncomputable section

namespace ProbabilityTheory.Wishart

variable {m n : ℕ}

/-- Effective column count `(m+2)s²/(mt−s²)` for a sample of positive dispersion,
where `s = tr(M Mᵀ)` and `t = tr((M Mᵀ)²)`. Division at zero is not a fit. -/
def effectiveCount (M : Fin m → Fin n → ℝ) : ℝ := (m + 2) * firstTrace M ^ 2 / dispersion M

/-- Fitted entry variance `s/(m k)` for a sample of positive dispersion, where `k` is the
effective count. This estimates a variance, not a standard deviation. -/
def fittedVariance (M : Fin m → Fin n → ℝ) : ℝ := firstTrace M / (m * effectiveCount M)

private lemma fit {m s t : ℝ} (hm : 0 < m) (hs : 0 < s) (hd : 0 < m * t - s ^ 2) :
    let k := (m + 2) * s ^ 2 / (m * t - s ^ 2)
    let w := s / (m * k)
    0 < k ∧ 0 < w ∧ ∀ r u : ℝ, (0 < r ∧ s = m * r * u ∧
      2 * t + s ^ 2 = m * (m + 2) * r * (r + 2) * u ^ 2) ↔ r = k ∧ u = w := by
  dsimp only
  let k := (m + 2) * s ^ 2 / (m * t - s ^ 2)
  have hk : 0 < k := div_pos (by positivity) hd
  have hk' : k * (m * t - s ^ 2) = (m + 2) * s ^ 2 := div_mul_cancel₀ _ hd.ne'
  refine ⟨hk, div_pos hs (mul_pos hm hk), fun r u => ⟨?_, ?_⟩⟩
  · rintro ⟨hr, h₁, h₂⟩
    have hr' : r * (m * t - s ^ 2) = (m + 2) * s ^ 2 := by
      rw [h₁] at h₂ ⊢
      linear_combination (m * r / 2) * h₂
    have hrk : r = k := (eq_div_iff hd.ne').2 hr'
    refine ⟨hrk, ?_⟩
    change u = s / (m * k)
    rw [← hrk, eq_div_iff (mul_pos hm hr).ne', h₁]
    ring
  · rintro ⟨rfl, rfl⟩
    change 0 < k ∧ s = m * k * (s / (m * k)) ∧ _
    refine ⟨hk, ?_, ?_⟩
    · field_simp
    · change 2 * t + s ^ 2 = m * (m + 2) * k * (k + 2) * (s / (m * k)) ^ 2
      field_simp
      linear_combination 2 * hk'

/-- For a sample with `s = tr X`, `t = tr(X²)` and `mt − s² > 0`, the trace and both
fitted parameters are positive. The equations `s = mru` and `2t + s² = m(m+2)r(r+2)u²`
have exactly one solution among real `r > 0` and real `u`: `effectiveCount M` and
`fittedVariance M`. These right-hand sides evaluate the polynomial moment formulas at
`(r,u)`; the Gaussian integral identities themselves describe a natural number of columns. -/
theorem methodOfMoments (M : Fin m → Fin n → ℝ) (hd : 0 < dispersion M) :
    0 < firstTrace M ∧ 0 < effectiveCount M ∧ 0 < fittedVariance M ∧
    ∀ r u : ℝ, (0 < r ∧ firstTrace M = m * r * u ∧
      2 * secondTrace M + firstTrace M ^ 2 = (m : ℝ) * (m + 2) * r * (r + 2) * u ^ 2) ↔
      r = effectiveCount M ∧ u = fittedVariance M := by
  have hm : 0 < (m : ℝ) := by
    by_contra! h
    have he := le_antisymm h (Nat.cast_nonneg m)
    unfold dispersion at hd
    rw [he, zero_mul] at hd
    nlinarith [sq_nonneg (firstTrace M)]
  have hs : 0 < firstTrace M := by
    refine lt_of_le_of_ne (gram_posSemidef M).trace_nonneg fun he => ?_
    have hz := (gram_posSemidef M).trace_eq_zero_iff.mp he.symm
    simp [dispersion, firstTrace, secondTrace, hz] at hd
  exact ⟨hs, fit hm hs hd⟩

end ProbabilityTheory.Wishart
