/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScore

/-!
# Polygenic inflation, stratification, and the attenuation ratio

Consequences of the exact LD-score identity of `LDScore` (Bulik-Sullivan et al. 2015).

## Polygenic inflation

Averaging `𝔼[χ² j] = N h² / M * ℓ j + (1 - h²)` over the `M` markers of a standardized genotype
matrix gives the mean inflation `(1 / M) ∑ j, 𝔼[χ² j] = 1 - h² + N h² ℓ̄ / M`, with `ℓ̄` the mean
LD score (`mean_integral_chiSq`): polygenicity alone inflates the mean association statistic
in proportion to `N`.

## Stratification

Bulik-Sullivan et al. (2015) add a term `N a` to the expected statistic for confounding such as
population stratification. We derive such a term exactly in a simple model: the phenotype has
an additional fixed (non-genetic) shift `s * c i` along a stratification axis
`c : Fin N → ℝ` (for example, a mean difference between ancestry groups),
`y = X β + ε + s c` (`phenoStrat`). For a probability measure and mean-zero effects and noise,

  `𝔼[χ² j] = N h² / M * ℓ j + (1 - h²) * (∑ i, X i j ^ 2) / N + N s² (X_jᵀ c / N)²`

(`integral_chiSqStrat`): stratification adds `N s² r_j²`, where `r_j = X_jᵀ c / N` is the
normalized cross product of marker `j` with the axis. Unlike the paper's `N a`, this term varies
across markers; it is constant only when every `r_j²` is (`integral_chiSqStrat_of_const`).

## Attenuation ratio

Loh et al. (2018) summarize LD-score regression output by the attenuation ratio
`(intercept - 1) / (mean χ² - 1)` (`attenuationRatio`), read as the share of the mean inflation
not explained by polygenicity. When the stratification term is a constant `N a`, the expected
statistic is exactly affine in the LD score with intercept `1 - h² + N a`; then the ratio of
expected values is `(N a - h²) / (N h² ℓ̄ / M + N a - h²)` (`attenuationRatio_of_const`). The
`-h²` terms come from the exact null level `1 - h²` of the model (see `LDScore`); measured from
that level instead of `1`, the confounding share is `N a / (N a + N h² ℓ̄ / M)`, which lies in
`[0, 1]` (`confoundingShare_of_const`, `confoundingShare_mem_Icc`).

## References

* B. K. Bulik-Sullivan, P.-R. Loh, H. K. Finucane, S. Ripke, J. Yang, Schizophrenia Working
  Group of the Psychiatric Genomics Consortium, N. Patterson, M. J. Daly, A. L. Price,
  B. M. Neale, *LD Score regression distinguishes confounding from polygenicity in
  genome-wide association studies*, Nat. Genet. 47 (2015), 291–295.
* P.-R. Loh, G. Kichaev, S. Gazal, A. P. Schoech, A. L. Price, *Mixed-model association for
  biobank-scale datasets*, Nat. Genet. 50 (2018), 906–908.
-/

@[expose] public section

open MeasureTheory MathlibExt.Biology.StatisticalGenetics.LDScore

namespace MathlibExt.Biology.StatisticalGenetics.LDScoreInflation

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {N M : ℕ}

/-- The mean LD score `ℓ̄ = (1 / M) ∑ j, ℓ j`. -/
noncomputable def meanLDScore (X : Matrix (Fin N) (Fin M) ℝ) : ℝ := (∑ j, ldScore X j) / M

/-- Polygenic inflation: for a standardized genotype matrix with `N, M ≠ 0`, the mean expected
association statistic is `1 - h² + N h² ℓ̄ / M`. -/
theorem mean_integral_chiSq (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0)
    (hM : M ≠ 0) (hX : IsStandardized X) :
    (∑ j, ∫ ω, D.chiSq X j ω ∂μ) / M = 1 - D.h2 + N * D.h2 / M * meanLDScore X := by
  simp_rw [D.integral_chiSq_of_standardized X hN _ hX]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, meanLDScore]
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  field_simp
  ring

/-- The phenotype with a stratification shift: `y i = (X β) i + ε i + s * c i`. -/
def phenoStrat (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ) (s : ℝ) (c : Fin N → ℝ)
    (i : Fin N) (ω : Ω) : ℝ := D.pheno X i ω + s * c i

/-- The `N`-normalized score of marker `j` under stratification, `X_jᵀ y / N`. -/
noncomputable def betaHatStrat (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ) (s : ℝ)
    (c : Fin N → ℝ) (j : Fin M) (ω : Ω) : ℝ := (∑ i, X i j * phenoStrat D X s c i ω) / N

/-- The association statistic `N * β̂ j ^ 2` under stratification. -/
noncomputable def chiSqStrat (D : Model μ N M) (X : Matrix (Fin N) (Fin M) ℝ) (s : ℝ)
    (c : Fin N → ℝ) (j : Fin M) (ω : Ω) : ℝ := N * betaHatStrat D X s c j ω ^ 2

/-- Stratification inflation: for a probability measure and mean-zero effects and noise,
`𝔼[χ² j] = N h² / M * ℓ j + (1 - h²) (∑ i, X i j ^ 2) / N + N s² (X_jᵀ c / N)²`. -/
theorem integral_chiSqStrat [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0)
    (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ) (c : Fin N → ℝ) (j : Fin M) :
    ∫ ω, chiSqStrat D X s c j ω ∂μ =
      N * D.h2 / M * ldScore X j + (1 - D.h2) * (∑ i, X i j ^ 2) / N +
        N * s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 := by
  set r := (∑ i, X i j * c i) / N with hr
  have hb : ∀ ω, betaHatStrat D X s c j ω = D.betaHat X j ω + s * r := fun ω => by
    simp only [betaHatStrat, phenoStrat, Model.betaHat, hr, mul_add, Finset.sum_add_distrib,
      add_div, mul_div_assoc', Finset.mul_sum, mul_left_comm (s : ℝ)]
  have hmem : MemLp (D.betaHat X j) 2 μ := by
    have hp : ∀ i, MemLp (D.pheno X i) 2 μ := fun i =>
      (memLp_finsetSum Finset.univ fun k _ => (D.memLp_beta k).const_mul (X i k)).add
        (D.memLp_eps i)
    have h := memLp_finsetSum Finset.univ fun i _ => (hp i).const_mul (X i j)
    have e : D.betaHat X j = fun ω => (N : ℝ)⁻¹ * ∑ i, X i j * D.pheno X i ω := by
      funext ω
      rw [Model.betaHat, div_eq_inv_mul]
    rw [e]
    exact h.const_mul _
  have hint : Integrable (D.betaHat X j) μ := hmem.integrable one_le_two
  have hzero : ∫ ω, D.betaHat X j ω ∂μ = 0 := by
    have hβi : ∀ k, Integrable (D.beta k) μ := fun k => (D.memLp_beta k).integrable one_le_two
    have hεi : ∀ i, Integrable (D.eps i) μ := fun i => (D.memLp_eps i).integrable one_le_two
    have hpi : ∀ i, Integrable (D.pheno X i) μ := fun i =>
      (integrable_finsetSum _ fun k _ => (hβi k).const_mul (X i k)).add (hεi i)
    have hp0 : ∀ i, ∫ ω, D.pheno X i ω ∂μ = 0 := fun i => by
      unfold Model.pheno
      rw [integral_add (integrable_finsetSum _ fun k _ => (hβi k).const_mul (X i k)) (hεi i),
        integral_finsetSum _ fun k _ => (hβi k).const_mul (X i k)]
      simp [integral_const_mul, hβ, hε]
    unfold Model.betaHat
    rw [integral_div, integral_finsetSum _ fun i _ => (hpi i).const_mul (X i j)]
    simp [integral_const_mul, hp0]
  have hc : ∀ ω, chiSqStrat D X s c j ω =
      D.chiSq X j ω + (2 * N * s * r) * D.betaHat X j ω + N * s ^ 2 * r ^ 2 := fun ω => by
    rw [chiSqStrat, hb, Model.chiSq]
    ring
  simp_rw [hc]
  have hchi : Integrable (fun ω => D.chiSq X j ω) μ := hmem.integrable_sq.const_mul (N : ℝ)
  have i1 : Integrable (fun ω => D.chiSq X j ω + (2 * N * s * r) * D.betaHat X j ω) μ :=
    hchi.add (hint.const_mul _)
  rw [integral_add i1 (integrable_const _),
    integral_add hchi (hint.const_mul _), integral_const_mul, hzero, integral_const,
    D.integral_chiSq X j]
  simp

/-- Stratification inflation for a standardized genotype matrix and `N ≠ 0`:
`𝔼[χ² j] = N h² / M * ℓ j + (1 - h²) + N s² (X_jᵀ c / N)²`. -/
theorem integral_chiSqStrat_of_standardized [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hX : IsStandardized X)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) (j : Fin M) :
    ∫ ω, chiSqStrat D X s c j ω ∂μ =
      N * D.h2 / M * ldScore X j + (1 - D.h2) + N * s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 := by
  rw [integral_chiSqStrat D X hβ hε, (hX j).2, mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr hN)]

/-- With a constant stratification term (`s² (X_jᵀ c / N)² = a` for every marker), the expected
statistic is exactly affine in the LD score, with slope `N h² / M` and intercept
`1 - h² + N a`. -/
theorem integral_chiSqStrat_of_const [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hX : IsStandardized X)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) (j : Fin M) :
    ∫ ω, chiSqStrat D X s c j ω ∂μ = N * D.h2 / M * ldScore X j + (1 - D.h2 + N * a) := by
  rw [integral_chiSqStrat_of_standardized D X hN hX hβ hε, ← ha j]
  ring

/-- With a constant stratification term `N a`, the mean expected statistic is
`N h² ℓ̄ / M + (1 - h² + N a)`. -/
theorem mean_integral_chiSqStrat_of_const [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hM : M ≠ 0) (hX : IsStandardized X)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) :
    (∑ j, ∫ ω, chiSqStrat D X s c j ω ∂μ) / M =
      N * D.h2 / M * meanLDScore X + (1 - D.h2 + N * a) := by
  simp_rw [integral_chiSqStrat_of_const D X hN hX hβ hε s c ha]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, meanLDScore]
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  field_simp

/-- The attenuation ratio `(intercept - 1) / (mean χ² - 1)` of Loh et al. (2018). -/
noncomputable def attenuationRatio (intercept meanChiSq : ℝ) : ℝ :=
  (intercept - 1) / (meanChiSq - 1)

/-- With a constant stratification term `N a`, the attenuation ratio of the exact intercept
`1 - h² + N a` and the mean expected statistic is `(N a - h²) / (N h² ℓ̄ / M + N a - h²)`. -/
theorem attenuationRatio_of_const [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hM : M ≠ 0) (hX : IsStandardized X)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) :
    attenuationRatio (1 - D.h2 + N * a) ((∑ j, ∫ ω, chiSqStrat D X s c j ω ∂μ) / M) =
      (N * a - D.h2) / (N * D.h2 / M * meanLDScore X + N * a - D.h2) := by
  rw [attenuationRatio, mean_integral_chiSqStrat_of_const D X hN hM hX hβ hε s c ha]
  congr 1 <;> ring

/-- With a constant stratification term `N a`, the share of the mean inflation above the exact
null level `1 - h²` that is due to stratification is `N a / (N a + N h² ℓ̄ / M)`. -/
theorem confoundingShare_of_const [IsProbabilityMeasure μ] (D : Model μ N M)
    (X : Matrix (Fin N) (Fin M) ℝ) (hN : N ≠ 0) (hM : M ≠ 0) (hX : IsStandardized X)
    (hβ : ∀ k, ∫ ω, D.beta k ω ∂μ = 0) (hε : ∀ i, ∫ ω, D.eps i ω ∂μ = 0) (s : ℝ)
    (c : Fin N → ℝ) {a : ℝ} (ha : ∀ j, s ^ 2 * ((∑ i, X i j * c i) / N) ^ 2 = a) :
    ((1 - D.h2 + N * a) - (1 - D.h2)) /
        ((∑ j, ∫ ω, chiSqStrat D X s c j ω ∂μ) / M - (1 - D.h2)) =
      N * a / (N * a + N * D.h2 / M * meanLDScore X) := by
  rw [mean_integral_chiSqStrat_of_const D X hN hM hX hβ hε s c ha]
  congr 1 <;> ring

/-- The confounding share `N a / (N a + N h² ℓ̄ / M)` lies in `[0, 1]` when `a`, `h²` and `ℓ̄`
are nonnegative (as they are in the model: `a` is a square, `h² ≥ 0` by `Model.h2_nonneg`,
LD scores are sums of squares). -/
theorem confoundingShare_mem_Icc {a h2 lbar : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h2) (hl : 0 ≤ lbar) :
    N * a / (N * a + N * h2 / M * lbar) ∈ Set.Icc 0 1 := by
  have h1 : 0 ≤ (N : ℝ) * a := by positivity
  have h2' : 0 ≤ (N : ℝ) * h2 / M * lbar := by positivity
  exact ⟨div_nonneg h1 (by linarith), div_le_one_of_le₀ (by linarith) (by linarith)⟩

end MathlibExt.Biology.StatisticalGenetics.LDScoreInflation
