/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.GREMLREML

/-! # Tests for `MathlibExt.Biology.StatisticalGenetics.GREMLREML`

Fixture: two sib pairs (four individuals) with an intercept. The relationship matrix `K₀` has
blocks `[1, 1/2; 1/2, 1]`. The contrast `B₀` has orthonormal rows `(1, 1, -1, -1) / 2`,
`(1, -1, 0, 0) / √2`, `(0, 0, 1, -1) / √2`; it annihilates the intercept and diagonalizes `K₀`
with eigenvalues `d₀ = (3/2, 1/2, 1/2)`, a two-level spectrum.

For `y₀ = (2, -2, 1, 1)`, `w = B₀ y₀ = (-1, 2√2, 0)`, so the class means of `w_i²` are `1` and
`4`, and the closed-form REML estimate is `(σ̂²_g, σ̂²_e) = (-3, 11/2)`: a negative genetic
variance, so the estimate is unconstrained. Both REML scores vanish there and not at `(1, 1)`;
these are computed from the definitions. For `y₁ = (1, -1, 0, 0)` the class mean `m_a` is `0`
and the closed form leaves the positive-definite region, so `0 < m_a` is needed. At `θ = (0, 0)`
the restricted log-likelihood is the junk value `0` and differs from the spectral form, so the
positivity hypothesis of `remlLogLik_gremlCov` is needed; both scores are also the junk value `0`
there, so `integral_scoreG` and `integral_scoreE` assume positive contrast variances.
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory WithLp
open MathlibExt.Probability.Statistics.LinearModel
open MathlibExt.Biology.StatisticalGenetics.GREMLREML

namespace MathlibExtTest.Biology.StatisticalGenetics.GREMLREML

/-- `1 / √2`. -/
noncomputable def c : ℝ := (Real.sqrt 2)⁻¹

theorem c_mul_c : c * c = 1 / 2 := by
  rw [c, ← mul_inv, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- Intercept-only design for four individuals. -/
def X₀ : Matrix (Fin 4) (Fin 1) ℝ := Matrix.of fun _ _ => 1

/-- Relationship matrix of two sib pairs. -/
noncomputable def K₀ : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1/2, 0, 0; 1/2, 1, 0, 0; 0, 0, 1, 1/2; 0, 0, 1/2, 1]

/-- Orthonormal error contrast diagonalizing `K₀`. -/
noncomputable def B₀ : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1/2, 1/2, -1/2, -1/2; c, -c, 0, 0; 0, 0, c, -c]

/-- Eigenvalues of `K₀` on the contrast space. -/
noncomputable def d₀ : Fin 3 → ℝ := ![3/2, 1/2, 1/2]

theorem isSpectralContrast₀ : IsSpectralContrast X₀ K₀ B₀ d₀ where
  mul_eq_zero := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B₀, X₀, Matrix.mul_apply, Fin.sum_univ_succ]
    norm_num
  mul_transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B₀, Matrix.mul_apply, Fin.sum_univ_succ, one_apply] <;> nlinarith [c_mul_c]
  card_add_card := by simp
  mul_mul_transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B₀, K₀, d₀, Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith [c_mul_c]

/-- `K₀ = I / 2 + V₀ V₀ᵀ / 2` with the family-indicator matrix `V₀`. -/
def V₀ : Matrix (Fin 4) (Fin 2) ℝ := !![1, 0; 1, 0; 0, 1; 0, 1]

theorem K₀_eq : K₀ = (1/2 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) + (1/2 : ℝ) • (V₀ * V₀ᵀ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K₀, V₀, Fin.sum_univ_succ, one_apply, vecMul, dotProduct] <;> norm_num

/-- The GREML covariance of the fixture is positive semidefinite for nonnegative components. -/
theorem posSemidef_gremlCov₀ {θ : ℝ × ℝ} (h1 : 0 ≤ θ.1) (h2 : 0 ≤ θ.2) :
    (gremlCov K₀ θ).PosSemidef := by
  have hV : (V₀ * V₀ᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose V₀
  have hK : K₀.PosSemidef := by
    rw [K₀_eq]
    exact (PosSemidef.one.smul (by norm_num)).add (hV.smul (by norm_num))
  exact (hK.smul h1).add (PosSemidef.one.smul h2)

/-! ### The closed-form estimate on concrete data, computed from the definitions -/

/-- Phenotypes with `w = B₀ y₀ = (-1, 2√2, 0)`. -/
def y₀ : Fin 4 → ℝ := ![2, -2, 1, 1]

theorem B₀_y₀ : B₀ *ᵥ y₀ = ![-1, 4 * c, 0] := by
  ext i
  fin_cases i <;> simp [B₀, y₀, mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem classSet_a : classSet d₀ (3/2) = {0} := by
  ext i; fin_cases i <;> simp [classSet, d₀] <;> norm_num

theorem classSet_b : classSet d₀ (1/2) = {1, 2} := by
  ext i; fin_cases i <;> simp [classSet, d₀]
  norm_num

theorem groupMean_a : groupMean d₀ (B₀ *ᵥ y₀) (3/2) = 1 := by
  rw [groupMean, groupSS, groupCount, classSet_a, B₀_y₀]
  simp

theorem groupMean_b : groupMean d₀ (B₀ *ᵥ y₀) (1/2) = 4 := by
  rw [groupMean, groupSS, groupCount, classSet_b, B₀_y₀]
  simp
  nlinarith [c_mul_c]

/-- The closed-form REML estimate is `(σ̂²_g, σ̂²_e) = (-3, 11/2)`: a negative genetic variance. -/
theorem twoLevelREML₀ : twoLevelREML d₀ (B₀ *ᵥ y₀) (3/2) (1/2) = (-3, 11/2) := by
  simp only [twoLevelREML, groupMean_a, groupMean_b]
  norm_num

/-- Both REML scores vanish at `(-3, 11/2)`, where `λ = (1, 4, 4)`, computed from the
definitions. -/
theorem score_at_estimate :
    scoreG d₀ ![-1, 4 * c, 0] (-3, 11/2) = 0 ∧ scoreE d₀ ![-1, 4 * c, 0] (-3, 11/2) = 0 := by
  have hc : (4 * c) ^ 2 = 8 := by nlinarith [c_mul_c]
  constructor <;> simp [scoreG, scoreE, contrastVar, d₀, Fin.sum_univ_succ, hc] <;> norm_num

/-- The `σ²_e` score does not vanish at `(1, 1)`, so `score_at_estimate` is not trivial. -/
theorem scoreE_at_one_one : scoreE d₀ ![-1, 4 * c, 0] (1, 1) ≠ 0 := by
  have hc : (4 * c) ^ 2 = 8 := by nlinarith [c_mul_c]
  simp [scoreE, contrastVar, d₀, Fin.sum_univ_succ, hc]
  norm_num

/-- The general theorem applies to the fixture: `(-3, 11/2)` is the unique maximizer of the
GREML restricted log-likelihood over the positive-definite region. -/
example : IsMaxOn (fun θ => remlLogLik B₀ (gremlCov K₀ θ) y₀)
    {θ | ∀ i, 0 < contrastVar d₀ θ i} (-3, 11/2) := by
  have hd : ∀ i, d₀ i = 3/2 ∨ d₀ i = 1/2 := by
    intro i; fin_cases i <;> simp [d₀]
  have h := isMaxOn_remlLogLik_twoLevelREML isSpectralContrast₀.mul_transpose
    isSpectralContrast₀.mul_mul_transpose (y := y₀) (by norm_num) hd
    (by rw [groupMean_a]; norm_num) (by rw [groupMean_b]; norm_num)
  rw [twoLevelREML₀] at h
  exact h.2.1

/-- The score theorem applied to the fixture agrees with `score_at_estimate`. -/
example : scoreG d₀ (B₀ *ᵥ y₀) (-3, 11/2) = 0 ∧ scoreE d₀ (B₀ *ᵥ y₀) (-3, 11/2) = 0 := by
  have hd : ∀ i, d₀ i = 3/2 ∨ d₀ i = 1/2 := by
    intro i; fin_cases i <;> simp [d₀]
  have h := isMaxOn_remlLogLik_twoLevelREML isSpectralContrast₀.mul_transpose
    isSpectralContrast₀.mul_mul_transpose (y := y₀) (by norm_num) hd
    (by rw [groupMean_a]; norm_num) (by rw [groupMean_b]; norm_num)
  rw [twoLevelREML₀] at h
  exact score_eq_zero_of_isLocalMax_remlLogLik isSpectralContrast₀.mul_transpose
    isSpectralContrast₀.mul_mul_transpose h.1
    (h.2.1.isLocalMax ((isOpen_posContrastVar d₀).mem_nhds h.1))

/-! ### Boundary cases -/

/-- Phenotypes with `w = B₀ y₁ = (0, √2, 0)`: the class mean `m_a` is `0`. -/
def y₁ : Fin 4 → ℝ := ![1, -1, 0, 0]

theorem B₀_y₁ : B₀ *ᵥ y₁ = ![0, 2 * c, 0] := by
  ext i
  fin_cases i <;> simp [B₀, y₁, mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- **`0 < m_a` is needed.** For `y₁`, `m_a = 0` and the closed form gives the contrast variance
`0` to the first class, outside the positive-definite region. -/
theorem twoLevelREML₁_not_mem :
    ¬ ∀ i, 0 < contrastVar d₀ (twoLevelREML d₀ (B₀ *ᵥ y₁) (3/2) (1/2)) i := by
  have ha : groupMean d₀ (B₀ *ᵥ y₁) (3/2) = 0 := by
    rw [groupMean, groupSS, groupCount, classSet_a, B₀_y₁]
    simp
  intro h
  have h0 := h 0
  rw [(contrastVar_twoLevelREML (by norm_num) 0).1 (by simp [d₀]), ha] at h0
  exact lt_irrefl 0 h0

/-- **Positive contrast variances are needed in `remlLogLik_gremlCov`.** At `θ = (0, 0)` the
covariance is `0`, the restricted log-likelihood is the junk value `0`, and the spectral form is
`-(3/2) log 2π ≠ 0`. -/
theorem remlLogLik_zero_ne :
    remlLogLik B₀ (gremlCov K₀ (0, 0)) y₀ ≠ spectralLogLik d₀ (B₀ *ᵥ y₀) (0, 0) := by
  have h1 : remlLogLik B₀ (gremlCov K₀ (0, 0)) y₀ = 0 := by
    simp [remlLogLik, gremlCov, MetaMathlibExt.multivariateGaussianPDFReal]
  have h2 : spectralLogLik d₀ (B₀ *ᵥ y₀) (0, 0) = -(3 / 2 * Real.log (2 * Real.pi)) := by
    simp [spectralLogLik, contrastVar]
  rw [h1, h2]
  have : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.two_le_pi])
  linarith

/-- **Positive contrast variances are needed in `integral_scoreG` and `integral_scoreE`.** At
`θ = (0, 0)` every contrast variance is `0`, so both scores are the junk value `0` for every `w`
and are not REML derivatives there. -/
theorem score_zero_zero (w : Fin 3 → ℝ) : scoreG d₀ w (0, 0) = 0 ∧ scoreE d₀ w (0, 0) = 0 := by
  simp [scoreG, scoreE, contrastVar]

/-! ### Unbiasedness: the Gaussian hypotheses are satisfiable -/

/-- With `y ~ N(X₀ β, K₀ + I)` (the identity on the multivariate Gaussian law), the closed-form
estimator has mean `(1, 1)` and both scores have mean zero at `(1, 1)`. -/
example (β : Fin 1 → ℝ) :
    let μ := multivariateGaussian (toLp 2 (X₀ *ᵥ β)) (gremlCov K₀ (1, 1))
    (∫ x, (twoLevelREML d₀ (B₀ *ᵥ ofLp x) (3/2) (1/2)).1 ∂μ = 1 ∧
      ∫ x, (twoLevelREML d₀ (B₀ *ᵥ ofLp x) (3/2) (1/2)).2 ∂μ = 1) ∧
    ∫ x, scoreG d₀ (B₀ *ᵥ ofLp x) (1, 1) ∂μ = 0 ∧
    ∫ x, scoreE d₀ (B₀ *ᵥ ofLp x) (1, 1) ∂μ = 0 := by
  intro μ
  have hV := posSemidef_gremlCov₀ (θ := (1, 1)) (by norm_num) (by norm_num)
  have hθ : ∀ i, 0 < contrastVar d₀ (1, 1) i := fun i => by
    fin_cases i <;> norm_num [contrastVar, d₀]
  refine ⟨integral_twoLevelREML isSpectralContrast₀ hV β HasLaw.id (by norm_num)
      ⟨0, by simp [d₀]⟩ ⟨1, by simp [d₀]⟩,
    integral_scoreG isSpectralContrast₀ hV hθ β HasLaw.id,
    integral_scoreE isSpectralContrast₀ hV hθ β HasLaw.id⟩

/-! ### Other entry points -/

/-- Every orthonormal error contrast rotates into a diagonalizing one (here `B₀` itself). -/
example : ∃ (Q : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ), Q * Qᵀ = 1 ∧ Qᵀ * Q = 1 ∧
    IsSpectralContrast X₀ K₀ (Q * B₀) d ∧ (K₀.PosSemidef → ∀ i, 0 ≤ d i) :=
  exists_isSpectralContrast (by ext i j; fin_cases i <;> fin_cases j <;> simp [K₀])
    isSpectralContrast₀.mul_eq_zero isSpectralContrast₀.mul_transpose
    isSpectralContrast₀.card_add_card

/-- The GRM of any genotype matrix is positive semidefinite. -/
example (X : Matrix (Fin 3) (Fin 5) ℝ) :
    (Matrix.of (MathlibExt.Biology.StatisticalGenetics.GREML.grm X)).PosSemidef :=
  posSemidef_grm X

end MathlibExtTest.Biology.StatisticalGenetics.GREMLREML
