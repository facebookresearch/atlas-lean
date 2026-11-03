/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Positivity

/-!
# LD-score regression: the expected association statistic

Bulik-Sullivan et al. (2015) model a quantitative phenotype measured on `N` individuals and
`M` markers as `y = X β + ε`, where

* `X : Matrix (Fin N) (Fin M) ℝ` is the genotype matrix, whose columns are standardized
  (mean `0`, sum of squares `N`);
* the per-marker effects `β k` are random with raw second moments
  `𝔼[β k * β l] = (h² / M) * [k = l]`;
* the environmental noise `ε i` has raw second moments `𝔼[ε i * ε i'] = (1 - h²) * [i = i']`;
* effects and noise are orthogonal in `L²`, `𝔼[β k * ε i] = 0`.

These are raw (uncentered) second moments over an arbitrary measure; they are the covariance
matrices, and orthogonality is uncorrelatedness, when the measure is a probability measure and
effects and noise have mean zero, as in the cited model.

The `N`-normalized score of marker `j` is `β̂ j = X_jᵀ y / N`; for a standardized column
(`∑ i, X i j ^ 2 = N`) it is the marginal least-squares estimate of the effect of marker `j`,
whose denominator is `∑ i, X i j ^ 2` in general. The association statistic is
`χ² j = N * β̂ j ^ 2`. With the sample correlations
`r j k = X_jᵀ X_k / N` and the LD score `ℓ j = ∑ k, r j k ^ 2`, the exact finite-sample
expectation conditional on `X` (the expectation here is over `β` and `ε` with `X` fixed) is

  `𝔼[χ² j] = N h² / M * ℓ j + (1 - h²)`.

The paper's regression equation (with no confounding) is the approximation
`𝔼[χ² j] ≈ N h² ℓ j / M + 1`; the exact identity under the same model differs from it by the
term `-h²` (the residual variance is `1 - h²`, not `1`), which is negligible only when the
total heritability `h²` is small; it is not controlled by the per-marker heritability `h² / M`
(for fixed `h²` the discrepancy stays `-h²` however large `M` is). We prove the exact
identity.

Only second moments enter the derivation, so only second-moment assumptions are made;
independent effects and noise with mean zero satisfy them. The heritability is not assumed to
lie in `[0, 1]`: this follows from the model when `N` and `M` are positive (`Model.h2_nonneg`,
`Model.h2_le_one`), and the identities hold for every model. Divisions by `N` and `M` are
meaningful for `N, M ≥ 1`; for `N = 0` both sides of `Model.integral_chiSq` are `0` by the
convention `x / 0 = 0`.

## Main results

* `Model`: the random-effects model, at the level of second moments.
* `Model.h2_nonneg`, `Model.h2_le_one`: the model forces `0 ≤ h² ≤ 1`.
* `Model.integral_chiSq`: `𝔼[χ² j] = N h² / M * ℓ j + (1 - h²) * (∑ i, X i j ^ 2) / N` for
  any genotype matrix, with `β̂` the `N`-normalized score.
* `IsStandardized`: every marker column has mean `0` and sum of squares `N`; then `ldCorr` is
  the sample correlation (`IsStandardized.ldCorr_self`, `IsStandardized.ldCorr_sq_le_one`).
* `Model.integral_chiSq_of_standardized`: for a standardized genotype matrix,
  `𝔼[χ² j] = N h² / M * ℓ j + (1 - h²)`.

## References

* B. K. Bulik-Sullivan, P.-R. Loh, H. K. Finucane, S. Ripke, J. Yang, Schizophrenia Working
  Group of the Psychiatric Genomics Consortium, N. Patterson, M. J. Daly, A. L. Price,
  B. M. Neale, *LD Score regression distinguishes confounding from polygenicity in
  genome-wide association studies*, Nat. Genet. 47 (2015), 291–295.
-/

@[expose] public section

open MeasureTheory

namespace MathlibExt.Biology.StatisticalGenetics.LDScore

variable {N M : ℕ}

/-- The normalized cross product `r j k = X_jᵀ X_k / N` of markers `j` and `k`. For a
standardized genotype matrix (`IsStandardized`) it is the sample correlation of the two
markers; for other matrices it is only a scale-dependent dot product. -/
noncomputable def ldCorr (X : Matrix (Fin N) (Fin M) ℝ) (j k : Fin M) : ℝ :=
  (∑ i, X i j * X i k) / N

/-- The LD score `ℓ j = ∑ k, r j k ^ 2` of marker `j` (an LD score in the sense of the cited
paper for a standardized genotype matrix). -/
noncomputable def ldScore (X : Matrix (Fin N) (Fin M) ℝ) (j : Fin M) : ℝ :=
  ∑ k, ldCorr X j k ^ 2

/-- The genotype matrix is standardized: every marker column has mean `0` and sum of squares
`N` (unit sample variance). -/
def IsStandardized (X : Matrix (Fin N) (Fin M) ℝ) : Prop :=
  ∀ k, ∑ i, X i k = 0 ∧ ∑ i, X i k ^ 2 = N

/-- For a standardized matrix each marker has correlation `1` with itself. -/
theorem IsStandardized.ldCorr_self {X : Matrix (Fin N) (Fin M) ℝ} (hX : IsStandardized X)
    (hN : N ≠ 0) (k : Fin M) : ldCorr X k k = 1 := by
  have h := (hX k).2
  simp only [pow_two] at h
  rw [ldCorr, h, div_self (Nat.cast_ne_zero.mpr hN)]

/-- For a standardized matrix the correlations lie in `[-1, 1]` (Cauchy–Schwarz). -/
theorem IsStandardized.ldCorr_sq_le_one {X : Matrix (Fin N) (Fin M) ℝ} (hX : IsStandardized X)
    (j k : Fin M) : ldCorr X j k ^ 2 ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [ldCorr]
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => X i j) (fun i => X i k)
  rw [(hX j).2, (hX k).2] at hcs
  rw [ldCorr, div_pow, div_le_one (by positivity)]
  nlinarith

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The random-effects model of LD-score regression (Bulik-Sullivan et al. 2015), stated at
the level of raw second moments, for `N` individuals and `M` markers with heritability `h2`.

* `beta k` is the (random) effect of marker `k`, with `∫ β k * β l = h2 / M * [k = l]`;
* `eps i` is the environmental noise of individual `i`, with
  `∫ ε i * ε i' = (1 - h2) * [i = i']`;
* effects and noise are orthogonal in `L²`.

The measure is arbitrary and no means are assumed; for a probability measure and mean-zero
effects and noise these are the covariance conditions of the cited model. The genotype matrix is
not part of the model: all expectations are conditional on it. -/
structure Model (μ : Measure Ω) (N M : ℕ) where
  /-- The SNP heritability `h²`. -/
  h2 : ℝ
  /-- Random per-marker effect sizes. -/
  beta : Fin M → Ω → ℝ
  /-- Random environmental noise. -/
  eps : Fin N → Ω → ℝ
  /-- Effects are square integrable. -/
  memLp_beta : ∀ k, MemLp (beta k) 2 μ
  /-- Noise terms are square integrable. -/
  memLp_eps : ∀ i, MemLp (eps i) 2 μ
  /-- Raw second moments of the effects: `∫ β βᵀ = (h² / M) I`. -/
  integral_beta_mul : ∀ k l, ∫ ω, beta k ω * beta l ω ∂μ = if k = l then h2 / M else 0
  /-- Raw second moments of the noise: `∫ ε εᵀ = (1 - h²) I`. -/
  integral_eps_mul : ∀ i i', ∫ ω, eps i ω * eps i' ω ∂μ = if i = i' then 1 - h2 else 0
  /-- Effects and noise are orthogonal in `L²`: `∫ β εᵀ = 0`. -/
  integral_beta_mul_eps : ∀ k i, ∫ ω, beta k ω * eps i ω ∂μ = 0

namespace Model

variable {μ : Measure Ω} (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ)

/-- The heritability is nonnegative when there is at least one marker. -/
theorem h2_nonneg (hM : 0 < M) : 0 ≤ D.h2 := by
  have h := D.integral_beta_mul ⟨0, hM⟩ ⟨0, hM⟩
  rw [ite_eq_left rfl] at h
  have h0 : 0 ≤ ∫ ω, D.beta ⟨0, hM⟩ ω * D.beta ⟨0, hM⟩ ω ∂μ :=
    integral_nonneg fun ω => mul_self_nonneg _
  rw [h] at h0
  exact (div_nonneg_iff.1 h0).elim (fun h => h.1) fun h => by
    exact absurd h.2 (not_le.2 (Nat.cast_pos.2 hM))

/-- The heritability is at most `1` when there is at least one individual. -/
theorem h2_le_one (hN : 0 < N) : D.h2 ≤ 1 := by
  have h := D.integral_eps_mul ⟨0, hN⟩ ⟨0, hN⟩
  rw [ite_eq_left rfl] at h
  have h0 : 0 ≤ ∫ ω, D.eps ⟨0, hN⟩ ω * D.eps ⟨0, hN⟩ ω ∂μ :=
    integral_nonneg fun ω => mul_self_nonneg _
  linarith

/-- The phenotype `y = X β + ε`. -/
def pheno (i : Fin N) (ω : Ω) : ℝ := ∑ k, X i k * D.beta k ω + D.eps i ω

/-- The `N`-normalized score `β̂ j = X_jᵀ y / N` of marker `j`. For a standardized column
(`∑ i, X i j ^ 2 = N`) it is the marginal least-squares estimate of the effect of marker `j`;
in general that estimate has denominator `∑ i, X i j ^ 2` instead of `N`. -/
noncomputable def betaHat (j : Fin M) (ω : Ω) : ℝ := (∑ i, X i j * D.pheno X i ω) / N

/-- The association statistic `χ² j = N * β̂ j ^ 2` of marker `j`. -/
noncomputable def chiSq (j : Fin M) (ω : Ω) : ℝ := N * D.betaHat X j ω ^ 2

private theorem integral_weighted_sq {Ω ι : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [Fintype ι] [DecidableEq ι] (f : ι → Ω → ℝ) (a b : ι → ℝ)
    (hf : ∀ k, MemLp (f k) 2 μ)
    (hm : ∀ k l, ∫ ω, f k ω * f l ω ∂μ = if k = l then b k else 0) :
    ∫ ω, (∑ k, a k * f k ω) ^ 2 ∂μ = ∑ k, a k ^ 2 * b k := by
  classical
  have hp (k l : ι) : Integrable (fun ω => (a k * a l) * (f k ω * f l ω)) μ :=
    ((hf k).integrable_mul (hf l)).const_mul _
  have he (ω : Ω) : (∑ k, a k * f k ω) ^ 2 =
      ∑ k, ∑ l, (a k * a l) * (f k ω * f l ω) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun k _ =>
    integrable_finsetSum Finset.univ (fun l _ => hp k l))]
  simp_rw [integral_finsetSum Finset.univ (fun l _ => hp _ l)]
  simp_rw [integral_const_mul, hm, mul_ite, mul_zero]
  simp [pow_two]

private theorem betaHat_eq_sum {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {N M : ℕ} (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ) (j : Fin M) (ω : Ω) :
    D.betaHat X j ω =
      ∑ k, ldCorr X j k * D.beta k ω + ∑ i, (X i j / N) * D.eps i ω := by
  unfold betaHat pheno ldCorr
  simp_rw [mul_add, Finset.sum_add_distrib, add_div, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, div_mul_eq_mul_div, Finset.sum_div]

/-- The exact expectation of the association statistic built from the `N`-normalized score,
for an arbitrary genotype matrix:
`𝔼[χ² j] = N h² / M * ℓ j + (1 - h²) * (∑ i, X i j ^ 2) / N`. (For `N = 0` both sides are `0`
by the convention `x / 0 = 0`.) -/
theorem integral_chiSq (j : Fin M) :
    ∫ ω, D.chiSq X j ω ∂μ =
      N * D.h2 / M * ldScore X j + (1 - D.h2) * (∑ i, X i j ^ 2) / N := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [chiSq, ldCorr, ldScore]
  let f : Fin M ⊕ Fin N → Ω → ℝ := Sum.elim D.beta D.eps
  let a : Fin M ⊕ Fin N → ℝ := Sum.elim (ldCorr X j) (fun i => X i j / N)
  let b : Fin M ⊕ Fin N → ℝ := Sum.elim (fun _ => D.h2 / M) (fun _ => 1 - D.h2)
  have hf (k : Fin M ⊕ Fin N) : MemLp (f k) 2 μ := by
    cases k with
    | inl k => exact D.memLp_beta k
    | inr i => exact D.memLp_eps i
  have hm (k l : Fin M ⊕ Fin N) :
      ∫ ω, f k ω * f l ω ∂μ = if k = l then b k else 0 := by
    cases k with
    | inl k =>
      cases l with
      | inl l => simpa [f, b] using D.integral_beta_mul k l
      | inr i => simpa [f] using D.integral_beta_mul_eps k i
    | inr i =>
      cases l with
      | inl k => simpa [f, mul_comm] using D.integral_beta_mul_eps k i
      | inr i' => simpa [f, b] using D.integral_eps_mul i i'
  have he := integral_weighted_sq f a b hf hm
  simp only [Fintype.sum_sum_type, a, b, f, Sum.elim_inl, Sum.elim_inr] at he
  simp_rw [chiSq, betaHat_eq_sum]
  rw [integral_const_mul, he]
  simp_rw [← Finset.sum_mul, div_pow, ← Finset.sum_div]
  unfold ldScore
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  field_simp

/-- LD-score regression (Bulik-Sullivan et al. 2015): for a standardized genotype matrix
(`IsStandardized`, so that `ldCorr` is the sample correlation and `ldScore` the LD score) and
`N ≠ 0`, `𝔼[χ² j] = N h² / M * ℓ j + (1 - h²)`. The expected association statistic is affine in
the LD score, with slope `N h² / M` and intercept `1 - h²`. The proof uses only that column `j`
has sum of squares `N`; the rest of the standardization is what makes `ℓ j` an LD score. -/
theorem integral_chiSq_of_standardized (hN : N ≠ 0) (j : Fin M) (hX : IsStandardized X) :
    ∫ ω, D.chiSq X j ω ∂μ = N * D.h2 / M * ldScore X j + (1 - D.h2) := by
  rw [D.integral_chiSq X j, (hX j).2, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr hN)]

end Model

end MathlibExt.Biology.StatisticalGenetics.LDScore
