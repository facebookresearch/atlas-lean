/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Moments.Covariance
public import MathlibExt.Probability.Statistics.PCA

/-!
# Unbiasedness of the sample covariance

For random sample vectors `X i : Ω → (Fin d → ℝ)`, `i : Fin N`, stacked as the rows of a data
matrix, the unbiased sample covariance `MathlibExt.Probability.Statistics.PCA.sampleCov`,
`S = (N - 1)⁻¹ (center X)ᵀ (center X)`, has expectation `Σ` entrywise when `N ≥ 2` and the
samples are square-integrable, pairwise independent, and share the mean `m` and the covariance
matrix `Σ`. These hypotheses are weaker than i.i.d. sampling: only the first two moments are
common, and independence is pairwise rather than mutual.

The deterministic facts come from the existing API: `PCA.sampleCov_posSemidef` (`S` is positive
semidefinite) and `MathlibExt.Biology.Omics.CovarianceBridge.rank_sampleCov_le`
(`rank S ≤ N - 1`, so `rank S ≤ min d (N - 1)` with `Matrix.rank_le_width`).

No filtering-consistency or nonlinear Gaussianity conclusion is drawn:
these are the covariance foundations on which ensemble methods build,
not a convergence theorem for any filter.

## Key results

- `sampleCov_expectation`: `E[S] = Σ` entrywise, for pairwise-independent square-integrable
  samples with common mean and covariance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open MathlibExt.Probability.Statistics.PCA (colMean sampleCov sampleCov_apply)

namespace MathlibExt.Probability.SampleCovariance

/-- Entries of the sample covariance of the data matrix whose rows are the samples at `ω`. -/
theorem sampleCov_entry {N d : ℕ} {Ω : Type*} (X : Fin N → Ω → (Fin d → ℝ))
    (ω : Ω) (j k : Fin d) :
    sampleCov (Matrix.of fun i j' => X i ω j') j k =
    ((N : ℝ) - 1)⁻¹ * ∑ i, ((X i ω j - (∑ l, X l ω j) / (N : ℝ)) *
      (X i ω k - (∑ l, X l ω k) / (N : ℝ))) := by
  simp [sampleCov_apply, colMean]

private theorem sum_centered_mul_eq {N : ℕ} (hN0 : (N : ℝ) ≠ 0) (a b : Fin N → ℝ) :
    ∑ i, ((a i - (∑ l, a l) / (N : ℝ)) * (b i - (∑ l, b l) / (N : ℝ))) =
    (∑ i, a i * b i) - (N : ℝ) * (((∑ l, a l) / (N : ℝ)) * ((∑ l, b l) / (N : ℝ))) := by
  set Sa : ℝ := ∑ l, a l with hSa
  set Sb : ℝ := ∑ l, b l with hSb
  set abar : ℝ := Sa / (N : ℝ) with hAbar
  set bbar : ℝ := Sb / (N : ℝ) with hBbar
  have hNa : (N : ℝ) * abar = Sa := by
    rw [hAbar, hSa]
    field_simp
  have hNb : (N : ℝ) * bbar = Sb := by
    rw [hBbar, hSb]
    field_simp
  have hExpand : ∀ i : Fin N, (a i - abar) * (b i - bbar) =
      a i * b i - a i * bbar - abar * b i + abar * bbar := by
    intro i
    ring
  simp only [hExpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have h1 : (∑ i : Fin N, a i * bbar) = Sa * bbar := by
    rw [← Finset.sum_mul, ← hSa]
  have h2 : (∑ i : Fin N, abar * b i) = abar * Sb := by
    rw [← Finset.mul_sum, ← hSb]
  have h3 : (∑ _i : Fin N, abar * bbar) = (N : ℝ) * (abar * bbar) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [h1, h2, h3]
  have hSa' : Sa = (N : ℝ) * abar := hNa.symm
  have hSb' : Sb = (N : ℝ) * bbar := hNb.symm
  rw [hSa', hSb']
  ring

private theorem raw_offdiag_aux {N d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : Fin N → Ω → (Fin d → ℝ)} {m : Fin d → ℝ}
    (hMean : ∀ i j, ∫ ω, X i ω j ∂μ = m j)
    (hIndep : ∀ i j, i ≠ j → IndepFun (X i) (X j) μ)
    (hInt : ∀ i j, Integrable (fun ω => X i ω j) μ)
    {i l : Fin N} (hNe : i ≠ l) (j k : Fin d) :
    ∫ ω, (X i ω j) * (X l ω k) ∂μ = m j * m k := by
  have hInd : IndepFun (fun ω => X i ω j) (fun ω => X l ω k) μ := by
    have h0 := hIndep i l hNe
    have h1 := h0.comp (measurable_pi_apply j) (measurable_pi_apply k)
    simpa [Function.comp_def] using h1
  have hA : AEStronglyMeasurable (fun ω => X i ω j) μ :=
    (hInt i j).aestronglyMeasurable
  have hB : AEStronglyMeasurable (fun ω => X l ω k) μ :=
    (hInt l k).aestronglyMeasurable
  have hEq := hInd.integral_mul_eq_mul_integral hA hB
  simpa [Pi.mul_apply, hMean] using hEq

private theorem raw_diag_aux {N d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : Fin N → Ω → (Fin d → ℝ)} {m : Fin d → ℝ} {Sig : Matrix (Fin d) (Fin d) ℝ}
    (hMean : ∀ i j, ∫ ω, X i ω j ∂μ = m j)
    (hCov : ∀ i j k, cov[fun ω => X i ω j, fun ω => X i ω k; μ] = Sig j k)
    (hInt : ∀ i j, Integrable (fun ω => X i ω j) μ)
    (hInt2 : ∀ i j k, Integrable (fun ω => (X i ω j) * (X i ω k)) μ)
    (i : Fin N) (j k : Fin d) :
    ∫ ω, (X i ω j) * (X i ω k) ∂μ = Sig j k + m j * m k := by
  have hC : ∫ ω, (X i ω j - m j) * (X i ω k - m k) ∂μ = Sig j k := by
    have hCov' := hCov i j k
    unfold ProbabilityTheory.covariance at hCov'
    rw [hMean i j, hMean i k] at hCov'
    exact hCov'
  have hXY : Integrable (fun ω => (X i ω j) * (X i ω k)) μ := hInt2 i j k
  have hX : Integrable (fun ω => X i ω j) μ := hInt i j
  have hY : Integrable (fun ω => X i ω k) μ := hInt i k
  have hXc : Integrable (fun ω => (X i ω j) * (m k)) μ := hX.mul_const (m k)
  have hCY : Integrable (fun ω => (m j) * (X i ω k)) μ := hY.const_mul (m j)
  have hConst : Integrable (fun _ : Ω => (m j) * (m k)) μ := integrable_const _
  have hEq : ∀ ω : Ω, (X i ω j - m j) * (X i ω k - m k) =
      ((X i ω j) * (X i ω k) - (X i ω j) * (m k) - (m j) * (X i ω k) + (m j) * (m k)) := by
    intro ω
    ring
  simp only [hEq] at hC
  have hSub1 : Integrable (fun ω => (X i ω j) * (X i ω k) - (X i ω j) * (m k)) μ :=
    hXY.sub hXc
  have hSub2 : Integrable
      (fun ω => (X i ω j) * (X i ω k) - (X i ω j) * (m k) - (m j) * (X i ω k)) μ :=
    hSub1.sub hCY
  rw [integral_add hSub2 hConst, integral_sub hSub1 hCY, integral_sub hXY hXc] at hC
  rw [integral_mul_const _ _, integral_const_mul _ _, hMean i j, hMean i k] at hC
  have hConstInt : (∫ _ : Ω, (m j) * (m k) ∂μ) = (m j) * (m k) := by
    rw [integral_const, probReal_univ, one_smul]
  rw [hConstInt] at hC
  linarith

private theorem integrable_cross_aux {N d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : Fin N → Ω → (Fin d → ℝ)}
    (hIndep : ∀ i j, i ≠ j → IndepFun (X i) (X j) μ)
    (hInt : ∀ i j, Integrable (fun ω => X i ω j) μ)
    (hInt2 : ∀ i j k, Integrable (fun ω => (X i ω j) * (X i ω k)) μ)
    (i l : Fin N) (j k : Fin d) :
    Integrable (fun ω => (X i ω j) * (X l ω k)) μ := by
  by_cases h : i = l
  · subst h
    exact hInt2 _ _ _
  · have hInd : IndepFun (fun ω => X i ω j) (fun ω => X l ω k) μ := by
      have h0 := hIndep i l h
      have h1 := h0.comp (measurable_pi_apply j) (measurable_pi_apply k)
      simpa [Function.comp_def] using h1
    have hMul := hInd.integrable_mul (hInt i j) (hInt l k)
    exact hMul

/-- Unbiasedness, entrywise: for `N ≥ 2` square-integrable sample vectors in `Fin d → ℝ` that
are pairwise independent and share the mean `m` and the coordinate covariance matrix `Σ`, the
expectation of the sample covariance is `Σ`. The samples need not be identically distributed or
mutually independent. -/
theorem sampleCov_expectation {N d : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin N → Ω → (Fin d → ℝ)} {m : Fin d → ℝ} {Sig : Matrix (Fin d) (Fin d) ℝ}
    (hMean : ∀ i j, ∫ ω, X i ω j ∂μ = m j)
    (hCov : ∀ i j k, cov[fun ω => X i ω j, fun ω => X i ω k; μ] = Sig j k)
    (hIndep : ∀ i j, i ≠ j → IndepFun (X i) (X j) μ)
    (hInt : ∀ i j, Integrable (fun ω => X i ω j) μ)
    (hInt2 : ∀ i j k, Integrable (fun ω => (X i ω j) * (X i ω k)) μ)
    (j k : Fin d) :
    ∫ ω, sampleCov (Matrix.of fun i j' => X i ω j') j k ∂μ = Sig j k := by
  have hN0' : N ≠ 0 := by omega
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN0'
  have hNm1 : ((N : ℝ) - 1) ≠ 0 := by
    have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hPoint : ∀ ω : Ω, sampleCov (Matrix.of fun i j' => X i ω j') j k =
      ((N : ℝ) - 1)⁻¹ * ((∑ i, (X i ω j) * (X i ω k)) -
        (N : ℝ) * (((∑ l, X l ω j) / (N : ℝ)) * ((∑ l, X l ω k) / (N : ℝ)))) := by
    intro ω
    rw [sampleCov_entry]
    congr 1
    exact sum_centered_mul_eq hN0 _ _
  simp only [hPoint]
  rw [integral_const_mul]
  have hT_int : Integrable (fun ω => ∑ i, (X i ω j) * (X i ω k)) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hInt2 i j k)
  have hT_eq : (∫ ω, (∑ i, (X i ω j) * (X i ω k)) ∂μ) =
      (N : ℝ) * (Sig j k + m j * m k) := by
    rw [integral_finsetSum Finset.univ (fun i _ => hInt2 i j k)]
    have hEach : ∀ i : Fin N, (∫ ω, (X i ω j) * (X i ω k) ∂μ) = Sig j k + m j * m k :=
      fun i => raw_diag_aux hMean hCov hInt hInt2 i j k
    simp only [hEach]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hInner_int : ∀ i : Fin N,
      Integrable (fun ω => ∑ l, (X i ω j) * (X l ω k)) μ := by
    intro i
    exact integrable_finsetSum Finset.univ
      (fun l _ => integrable_cross_aux hIndep hInt hInt2 i l j k)
  have hD_int : Integrable (fun ω => ∑ i, ∑ l, (X i ω j) * (X l ω k)) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hInner_int i)
  have hU_eq_fun : (fun ω : Ω => ((∑ l, X l ω j) / (N : ℝ)) * ((∑ l, X l ω k) / (N : ℝ))) =
      (fun ω : Ω => ((N : ℝ)⁻¹ * (N : ℝ)⁻¹) * (∑ i, ∑ l, (X i ω j) * (X l ω k))) := by
    funext ω
    have hMul : (∑ i : Fin N, X i ω j) * (∑ l : Fin N, X l ω k) =
        ∑ i, ∑ l, (X i ω j) * (X l ω k) := by
      rw [Finset.sum_mul_sum]
    calc ((∑ l, X l ω j) / (N : ℝ)) * ((∑ l, X l ω k) / (N : ℝ))
        = ((N : ℝ)⁻¹ * (N : ℝ)⁻¹) * ((∑ i, X i ω j) * (∑ l, X l ω k)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
      _ = ((N : ℝ)⁻¹ * (N : ℝ)⁻¹) * (∑ i, ∑ l, (X i ω j) * (X l ω k)) := by
          rw [hMul]
  have hU_int : Integrable
      (fun ω : Ω => ((∑ l, X l ω j) / (N : ℝ)) * ((∑ l, X l ω k) / (N : ℝ))) μ := by
    rw [hU_eq_fun]
    exact hD_int.const_mul _
  have hD_eq0 : (∫ ω, (∑ i, ∑ l, (X i ω j) * (X l ω k)) ∂μ) =
      ∑ i, ∑ l, (∫ ω, (X i ω j) * (X l ω k) ∂μ) := by
    rw [integral_finsetSum Finset.univ (fun i _ => hInner_int i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum Finset.univ
      (fun l _ => integrable_cross_aux hIndep hInt hInt2 i l j k)]
  have hEach2 : ∀ i l : Fin N, (∫ ω, (X i ω j) * (X l ω k) ∂μ) =
      m j * m k + (if i = l then Sig j k else 0) := by
    intro i l
    by_cases h : i = l
    · subst h
      rw [raw_diag_aux hMean hCov hInt hInt2 _ j k]
      simp
      ring
    · rw [raw_offdiag_aux hMean hIndep hInt h j k]
      simp [h]
  simp only [hEach2] at hD_eq0
  have hDiag : ∀ i : Fin N, (∑ l : Fin N, (if i = l then Sig j k else 0)) = Sig j k := by
    intro i
    rw [Finset.sum_ite_eq]
    simp
  have hD_eq : (∫ ω, (∑ i, ∑ l, (X i ω j) * (X l ω k)) ∂μ) =
      (N : ℝ) * (Sig j k) + (N : ℝ) ^ 2 * (m j * m k) := by
    rw [hD_eq0]
    have hSplit : (∑ i : Fin N, ∑ l : Fin N, (m j * m k + (if i = l then Sig j k else 0))) =
        (∑ i : Fin N, ∑ _l : Fin N, (m j * m k)) +
        (∑ i : Fin N, ∑ l : Fin N, (if i = l then Sig j k else 0)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_add_distrib]
    rw [hSplit]
    have hConst2 : (∑ _i : Fin N, ∑ _l : Fin N, (m j * m k)) = (N : ℝ) ^ 2 * (m j * m k) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hDiagSum : (∑ i : Fin N, ∑ l : Fin N, (if i = l then Sig j k else 0)) =
        (N : ℝ) * (Sig j k) := by
      simp only [hDiag]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hConst2, hDiagSum]
    ring
  have hU_eq : (∫ ω, ((∑ l, X l ω j) / (N : ℝ)) * ((∑ l, X l ω k) / (N : ℝ)) ∂μ) =
      (Sig j k) / (N : ℝ) + m j * m k := by
    rw [hU_eq_fun, integral_const_mul, hD_eq]
    field_simp
  have hNU_int : Integrable
      (fun ω : Ω => (N : ℝ) * (((∑ l, X l ω j) / (N : ℝ)) * ((∑ l, X l ω k) / (N : ℝ)))) μ :=
    hU_int.const_mul _
  have hS_eq : (∫ ω, ((∑ i, (X i ω j) * (X i ω k)) -
      (N : ℝ) * (((∑ l, X l ω j) / (N : ℝ)) * ((∑ l, X l ω k) / (N : ℝ)))) ∂μ) =
      ((N : ℝ) - 1) * (Sig j k) := by
    rw [integral_sub hT_int hNU_int, integral_const_mul, hT_eq, hU_eq]
    field_simp
    ring
  calc ((N : ℝ) - 1)⁻¹ *
        (∫ ω, ((∑ i, (X i ω j) * (X i ω k)) -
          (N : ℝ) * (((∑ l, X l ω j) / (N : ℝ)) * ((∑ l, X l ω k) / (N : ℝ)))) ∂μ)
      = ((N : ℝ) - 1)⁻¹ * (((N : ℝ) - 1) * (Sig j k)) := by rw [hS_eq]
    _ = Sig j k := by field_simp

end MathlibExt.Probability.SampleCovariance
