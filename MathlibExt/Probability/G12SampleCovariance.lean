/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Moments.Covariance

/-!
# Ensemble covariance foundations

For a data matrix `X : Matrix (Fin N) (Fin d) ℝ` whose rows are
observations, the unbiased sample covariance is
`S = (N - 1)⁻¹ (center X)ᵀ (center X)`. This file proves `S` is
positive semidefinite, has rank at most `min d (N - 1)` for `N ≥ 2`
(the centered rows sum to zero, so one row direction is lost), and has
expectation equal to the population covariance `Σ` for independent
identically distributed square-integrable samples.

No filtering-consistency or nonlinear Gaussianity conclusion is drawn:
these are the covariance foundations on which ensemble methods build,
not a convergence theorem for any filter.

## Key results

- `g12SampleCov_posSemidef`: `S` is positive semidefinite.
- `g12SampleCov_rank_le`: `rank S ≤ min d (N - 1)` for `N ≥ 2`.
- `g12SampleCov_expectation`: `E[S] = Σ` entrywise, for i.i.d.
  square-integrable samples with common mean and covariance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix

namespace MathlibExt.Probability.G12SampleCovariance

/-- Column mean of a data matrix (rows are observations). -/
noncomputable def g12ColMean {N d : ℕ} (X : Matrix (Fin N) (Fin d) ℝ) (j : Fin d) : ℝ :=
  (∑ i, X i j) / N

/-- Centered data matrix. -/
noncomputable def g12Center {N d : ℕ} (X : Matrix (Fin N) (Fin d) ℝ) :
    Matrix (Fin N) (Fin d) ℝ :=
  Matrix.of fun i j => X i j - g12ColMean X j

/-- Unbiased sample covariance `(N - 1)⁻¹ (center X)ᵀ (center X)`. -/
noncomputable def g12SampleCov {N d : ℕ} (X : Matrix (Fin N) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  ((N : ℝ) - 1)⁻¹ • ((g12Center X)ᵀ * g12Center X)

/-- Entries of the sample covariance matrix. -/
theorem g12SampleCov_apply {N d : ℕ} (X : Matrix (Fin N) (Fin d) ℝ) (j k : Fin d) :
    g12SampleCov X j k =
      ((N : ℝ) - 1)⁻¹ * ∑ i, (X i j - g12ColMean X j) * (X i k - g12ColMean X k) := by
  simp [g12SampleCov, g12Center, Matrix.mul_apply, Finset.mul_sum]

/-- Sample covariance of any data matrix is positive semidefinite. -/
theorem g12SampleCov_posSemidef {N d : ℕ} (X : Matrix (Fin N) (Fin d) ℝ) :
    (g12SampleCov X).PosSemidef := by
  unfold g12SampleCov
  by_cases hN0 : N = 0
  · subst hN0
    have hZero : ((g12Center X)ᵀ * g12Center X) = 0 := by
      ext i j
      simp [Matrix.mul_apply]
    rw [hZero, smul_zero]
    exact Matrix.PosSemidef.zero
  · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
    have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
    have hNonneg : 0 ≤ ((N : ℝ) - 1)⁻¹ := by
      apply inv_nonneg.mpr
      linarith
    have hPSD : ((g12Center X)ᵀ * g12Center X).PosSemidef := by
      have h := Matrix.posSemidef_conjTranspose_mul_self (g12Center X)
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact hPSD.smul hNonneg

theorem g12Center_col_sum {N d : ℕ} (hN : N ≠ 0) (X : Matrix (Fin N) (Fin d) ℝ)
    (j : Fin d) : ∑ i, g12Center X i j = 0 := by
  simp only [g12Center, g12ColMean, Matrix.of_apply]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hSum : (∑ _i : Fin N, ((∑ i, X i j) / (N : ℝ))) = ∑ i, X i j := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul]
    field_simp
  rw [Finset.sum_sub_distrib]
  rw [hSum]
  exact sub_self _

theorem g12Center_transpose_mulVec_ones {N d : ℕ} (hN : N ≠ 0)
    (X : Matrix (Fin N) (Fin d) ℝ) :
    (g12Center X)ᵀ *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  ext j
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Matrix.transpose_apply, mul_one]
  exact g12Center_col_sum hN X j

/-- Rank bound: the sample covariance has rank at most `min d (N - 1)`
for `N ≥ 2` (centered rows sum to zero, so one row direction is lost). -/
theorem g12SampleCov_rank_le {N d : ℕ} (hN : 2 ≤ N) (X : Matrix (Fin N) (Fin d) ℝ) :
    (g12SampleCov X).rank ≤ min d (N - 1) := by
  unfold g12SampleCov
  have hN0 : N ≠ 0 := by omega
  have hNm1 : ((N : ℝ) - 1) ≠ 0 := by
    have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hc_ne : ((N : ℝ) - 1)⁻¹ ≠ 0 := inv_ne_zero hNm1
  have hc_mem : ((N : ℝ) - 1)⁻¹ ∈ nonZeroDivisors ℝ :=
    (mem_nonZeroDivisors_iff_ne_zero).mpr hc_ne
  rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ hc_mem]
  rw [Matrix.rank_transpose_mul_self]
  apply le_min
  · exact Matrix.rank_le_width _
  · have hRankEq : (g12Center X).rank = ((g12Center X)ᵀ).rank := by
      rw [Matrix.rank_transpose]
    rw [hRankEq]
    have hKer : (fun _ => (1 : ℝ)) ∈ LinearMap.ker ((g12Center X)ᵀ).mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      exact g12Center_transpose_mulVec_ones hN0 X
    have hOnesNe : (fun _ => (1 : ℝ) : Fin N → ℝ) ≠ 0 := by
      have hInh : Inhabited (Fin N) := ⟨⟨0, by omega⟩⟩
      intro h
      have := congrFun h (default : Fin N)
      simp at this
    have hNontriv : Nontrivial ↥(LinearMap.ker ((g12Center X)ᵀ).mulVecLin) := by
      refine ⟨⟨_, hKer⟩, 0, ?_⟩
      intro hEq
      apply hOnesNe
      have := congrArg Subtype.val hEq
      simpa using this
    have hPos : 0 < Module.finrank ℝ ↥(LinearMap.ker ((g12Center X)ᵀ).mulVecLin) :=
      (Module.finrank_pos_iff).mpr hNontriv
    have hAdd := LinearMap.finrank_range_add_finrank_ker ((g12Center X)ᵀ).mulVecLin
    have hFin : Module.finrank ℝ (Fin N → ℝ) = N := by
      rw [Module.finrank_pi]
      simp
    rw [hFin] at hAdd
    have hRankDef : ((g12Center X)ᵀ).rank =
        Module.finrank ℝ ↥(LinearMap.range ((g12Center X)ᵀ).mulVecLin) := rfl
    omega

theorem g12SampleCov_entry {N d : ℕ} {Ω : Type*} (X : Fin N → Ω → (Fin d → ℝ))
    (ω : Ω) (j k : Fin d) :
    g12SampleCov (Matrix.of fun i j' => X i ω j') j k =
    ((N : ℝ) - 1)⁻¹ * ∑ i, ((X i ω j - (∑ l, X l ω j) / (N : ℝ)) *
      (X i ω k - (∑ l, X l ω k) / (N : ℝ))) := by
  simp [g12SampleCov, g12Center, g12ColMean, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.transpose_apply, smul_eq_mul, Matrix.of_apply]

theorem sum_centered_mul_eq {N : ℕ} (hN0 : (N : ℝ) ≠ 0) (a b : Fin N → ℝ) :
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

theorem raw_offdiag_aux {N d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
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

theorem raw_diag_aux {N d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
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

theorem integrable_cross_aux {N d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
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

/-- Unbiasedness, entrywise: for independent identically distributed
square-integrable samples in `Fin d` with common mean `m` and common
covariance matrix `Σ` (entrywise covariance of coordinates), the
expectation of the sample covariance is `Σ`. Independence is stated
as pairwise independence of the sample vectors; identical distribution
is the `∀ i` mean/covariance hypotheses. -/
theorem g12SampleCov_expectation {N d : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin N → Ω → (Fin d → ℝ)} {m : Fin d → ℝ} {Sig : Matrix (Fin d) (Fin d) ℝ}
    (hMean : ∀ i j, ∫ ω, X i ω j ∂μ = m j)
    (hCov : ∀ i j k, cov[fun ω => X i ω j, fun ω => X i ω k; μ] = Sig j k)
    (hIndep : ∀ i j, i ≠ j → IndepFun (X i) (X j) μ)
    (hInt : ∀ i j, Integrable (fun ω => X i ω j) μ)
    (hInt2 : ∀ i j k, Integrable (fun ω => (X i ω j) * (X i ω k)) μ)
    (hIntMean : ∀ i j k, Integrable (fun ω => (X i ω j - m j) * (X i ω k - m k)) μ)
    (j k : Fin d) :
    ∫ ω, g12SampleCov (Matrix.of fun i j' => X i ω j') j k ∂μ = Sig j k := by
  have _hUse := hIntMean
  have hN0' : N ≠ 0 := by omega
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN0'
  have hNm1 : ((N : ℝ) - 1) ≠ 0 := by
    have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hPoint : ∀ ω : Ω, g12SampleCov (Matrix.of fun i j' => X i ω j') j k =
      ((N : ℝ) - 1)⁻¹ * ((∑ i, (X i ω j) * (X i ω k)) -
        (N : ℝ) * (((∑ l, X l ω j) / (N : ℝ)) * ((∑ l, X l ω k) / (N : ℝ)))) := by
    intro ω
    rw [g12SampleCov_entry]
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


end MathlibExt.Probability.G12SampleCovariance
