/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# LD-score regression: the expected association statistic

Bulik-Sullivan et al. (2015) model a quantitative phenotype measured on `N` individuals and
`M` markers as `y = X β + ε`, where

* `X : Matrix (Fin N) (Fin M) ℝ` is the genotype matrix, whose columns are standardized
  (mean `0`, sum of squares `N`);
* the per-marker effects `β k` are random with `𝔼[β k * β l] = (h² / M) * [k = l]`;
* the environmental noise `ε i` satisfies `𝔼[ε i * ε i'] = (1 - h²) * [i = i']`;
* effects and noise are uncorrelated, `𝔼[β k * ε i] = 0`.

The marginal least-squares estimate of the effect of marker `j` is `β̂ j = X_jᵀ y / N` and the
association statistic is `χ² j = N * β̂ j ^ 2`. With the sample correlations
`r j k = X_jᵀ X_k / N` and the LD score `ℓ j = ∑ k, r j k ^ 2`, the exact finite-sample
expectation conditional on `X` (the expectation here is over `β` and `ε` with `X` fixed) is

  `𝔼[χ² j] = N h² / M * ℓ j + (1 - h²)`.

The paper's regression equation (with no confounding) is the approximation
`𝔼[χ² j] ≈ N h² ℓ j / M + 1`; the exact identity under the same model differs from it by the
term `-h²` (the residual variance is `1 - h²`, not `1`), which is negligible when the
per-marker heritability is small. We prove the exact identity.

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
  any genotype matrix.
* `Model.integral_chiSq_of_standardized`: for a column with `∑ i, X i j ^ 2 = N`,
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

/-- Sample correlation `r j k = X_jᵀ X_k / N` between markers `j` and `k` (for standardized
columns of the genotype matrix `X`). -/
noncomputable def ldCorr (X : Matrix (Fin N) (Fin M) ℝ) (j k : Fin M) : ℝ :=
  (∑ i, X i j * X i k) / N

/-- The LD score `ℓ j = ∑ k, r j k ^ 2` of marker `j`. -/
noncomputable def ldScore (X : Matrix (Fin N) (Fin M) ℝ) (j : Fin M) : ℝ :=
  ∑ k, ldCorr X j k ^ 2

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The random-effects model of LD-score regression (Bulik-Sullivan et al. 2015), stated at
the level of second moments, for `N` individuals and `M` markers with heritability `h2`.

* `beta k` is the (random) effect of marker `k`, with `𝔼[β k * β l] = h2 / M * [k = l]`;
* `eps i` is the environmental noise of individual `i`, with
  `𝔼[ε i * ε i'] = (1 - h2) * [i = i']`;
* effects and noise are uncorrelated.

The genotype matrix is not part of the model: all expectations are conditional on it. -/
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
  /-- `Cov β = (h² / M) I`. -/
  integral_beta_mul : ∀ k l, ∫ ω, beta k ω * beta l ω ∂μ = if k = l then h2 / M else 0
  /-- `Cov ε = (1 - h²) I`. -/
  integral_eps_mul : ∀ i i', ∫ ω, eps i ω * eps i' ω ∂μ = if i = i' then 1 - h2 else 0
  /-- Effects and noise are uncorrelated. -/
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

/-- The marginal effect estimate `β̂ j = X_jᵀ y / N` of marker `j`. -/
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

/-- The exact expectation of the association statistic for an arbitrary genotype matrix:
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

/-- LD-score regression (Bulik-Sullivan et al. 2015): for a standardized marker `j`
(`∑ i, X i j ^ 2 = N`) and `N ≠ 0`, `𝔼[χ² j] = N h² / M * ℓ j + (1 - h²)`. The expected
association statistic is affine in the LD score, with slope `N h² / M` and intercept
`1 - h²`. -/
theorem integral_chiSq_of_standardized (hN : N ≠ 0) (j : Fin M)
    (hX : ∑ i, X i j ^ 2 = N) :
    ∫ ω, D.chiSq X j ω ∂μ = N * D.h2 / M * ldScore X j + (1 - D.h2) := by
  rw [D.integral_chiSq X j, hX, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr hN)]

end Model

end MathlibExt.Biology.StatisticalGenetics.LDScore
