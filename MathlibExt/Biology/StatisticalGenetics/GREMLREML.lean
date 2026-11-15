/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.GREML
public import MathlibExt.Probability.Statistics.LinearModel.REML

/-!
# GREML: the restricted maximum likelihood (REML) estimator of SNP heritability

GCTA's GREML (Yang et al. 2010, 2011) fits the variance components of the Gaussian linear mixed
model `y ~ N(X β, σ²_g K + σ²_e I)` by restricted maximum likelihood, where
`X : Matrix m k ℝ` holds the fixed effects (intercept, covariates) and `K` is a symmetric
relationship matrix, typically the GRM `A = X_g X_gᵀ / M` of
`MathlibExt.Biology.StatisticalGenetics.GREML` (positive semidefinite by `posSemidef_grm`).
`MathlibExt.Biology.StatisticalGenetics.GREML` treats Haseman–Elston regression, a moment
estimator; this file treats the REML estimator itself, using the restricted log-likelihood
`remlLogLik` of `MathlibExt.Probability.Statistics.LinearModel.REML` with the covariance
`gremlCov K (σ²_g, σ²_e) = σ²_g K + σ²_e I`.

**Spectral form.** Let `B : Matrix r m ℝ` be an error contrast with orthonormal rows that
diagonalizes the relationship matrix on the contrast space: `B X = 0`, `B Bᵀ = 1`,
`card r + card k = card m` and `B K Bᵀ = diag d` (`IsSpectralContrast`). Every orthonormal error
contrast `A` can be rotated into one, `B = Q A` with `Q` orthogonal and `d` the eigenvalues of
`A K Aᵀ`, nonnegative when `K` is positive semidefinite (`exists_isSpectralContrast`), and the
rotation does not change the criterion (`remlLogLik_eq_spectralLogLik_of_orthogonal`). With
`w = B y` and `λ_i(θ) = σ²_g d_i + σ²_e` (`contrastVar`), whenever every `λ_i(θ) > 0`,

  `ℓ_REML(θ) = -(r/2) log 2π - (1/2) ∑_i log λ_i(θ) - (1/2) ∑_i w_i² / λ_i(θ)`

(`remlLogLik_gremlCov`, `spectralLogLik`). This is the rotation used by FaST-LMM and GEMMA.

**Score equations.** The partial derivatives of `ℓ_REML` are
`∂ℓ/∂σ²_g = (1/2) ∑_i d_i (w_i² - λ_i) / λ_i²` and `∂ℓ/∂σ²_e = (1/2) ∑_i (w_i² - λ_i) / λ_i²`
(`scoreG`, `scoreE`, `hasDerivAt_spectralLogLik_fst`, `hasDerivAt_spectralLogLik_snd`), so a REML
estimate in the interior of the positive-definite region solves both equations
(`score_eq_zero_of_isLocalMax_remlLogLik`). With the REML projection
`P = Bᵀ (B V Bᵀ)⁻¹ B` (`remlProj`) these are GCTA's REML equations
`yᵀ P K P y = tr (P K)` and `yᵀ P P y = tr P` (`reml_equations_of_isLocalMax`; Yang et al.
2011, where `P` is written `V⁻¹ - V⁻¹ X (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹`; that this equals `remlProj` is not
proved here). The REML estimating equations are unbiased: if `y ~ N(X β, σ²_g K + σ²_e I)` at
`θ₀`, then `𝔼[w_i²] = λ_i(θ₀)` (`integral_sq_contrast`), and if moreover every `λ_i(θ₀) > 0`,
both scores have mean zero at `θ₀` (`integral_scoreG`, `integral_scoreE`).

**Closed form for two-level spectra.** When `d` takes exactly two values `a ≠ b` on the contrast
space (for example sib pairs with an intercept, where the GRM blocks `[1, 1/2; 1/2, 1]` give
`d ∈ {3/2, 1/2}`), the REML criterion separates into the two classes and is maximized at
`λ_a = m_a`, `λ_b = m_b`, the class means of `w_i²` (`groupMean`):

  `σ̂²_g = (m_a - m_b) / (a - b)`,  `σ̂²_e = (a m_b - b m_a) / (a - b)`  (`twoLevelREML`).

When `m_a, m_b > 0` this is the unique maximizer of `ℓ_REML` over the whole region where the
contrast covariance is positive definite (`isMaxOn_remlLogLik_twoLevelREML`), and it is unbiased
(`integral_twoLevelREML`). It is the unconstrained REML estimate: `σ̂²_g` can be negative
(the test file has an example); GCTA's boundary-constrained estimate is not treated.

Not covered: existence of a REML maximizer for general spectra, the average-information
algorithm itself, consistency or asymptotic normality of the REML estimator, and constrained
(boundary) estimates. Singular contrast covariances are excluded by hypothesis wherever a
result divides by a contrast variance (the spectral form, the score equations and their
unbiasedness), as in `remlLogLik`.

## Main results

* `gremlCov`, `contrastVar`, `spectralLogLik`, `IsSpectralContrast`: the GREML covariance, the
  contrast variances `σ²_g d_i + σ²_e`, the spectral REML criterion and diagonalizing contrasts.
* `remlLogLik_gremlCov`, `exists_isSpectralContrast`, `remlLogLik_eq_spectralLogLik_of_orthogonal`:
  the REML log-likelihood of GREML in spectral form.
* `scoreG`, `scoreE`, `score_eq_zero_of_isLocalMax_remlLogLik`, `reml_equations_of_isLocalMax`:
  the REML score equations, in spectral and in GCTA matrix form.
* `integral_sq_contrast`, `integral_scoreG`, `integral_scoreE`: unbiasedness of the scores.
* `twoLevelREML`, `isMaxOn_remlLogLik_twoLevelREML`, `integral_twoLevelREML`: the closed-form
  REML estimator for two-level spectra, its optimality and unbiasedness.
* `posSemidef_grm`: the GRM is positive semidefinite.

## References

* H. D. Patterson, R. Thompson, *Recovery of inter-block information when block sizes are
  unequal*, Biometrika 58 (1971), 545–554.
* J. Yang, B. Benyamin, B. P. McEvoy, et al., *Common SNPs explain a large proportion of the
  heritability for human height*, Nat. Genet. 42 (2010), 565–569.
* J. Yang, S. H. Lee, M. E. Goddard, P. M. Visscher, *GCTA: a tool for genome-wide complex trait
  analysis*, Am. J. Hum. Genet. 88 (2011), 76–82.
* C. Lippert, J. Listgarten, Y. Liu, et al., *FaST linear mixed models for genome-wide association
  studies*, Nat. Methods 8 (2011), 833–835.
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory WithLp
open MathlibExt.Probability.Statistics.LinearModel

namespace MathlibExt.Biology.StatisticalGenetics.GREMLREML

variable {m k r : Type*} [Fintype m] [Fintype k] [Fintype r] [DecidableEq m] [DecidableEq r]

/-! ### The GREML covariance and the spectral REML criterion -/

/-- The GREML phenotypic covariance `σ²_g K + σ²_e I` at `θ = (σ²_g, σ²_e)`. -/
noncomputable def gremlCov (K : Matrix m m ℝ) (θ : ℝ × ℝ) : Matrix m m ℝ :=
  θ.1 • K + θ.2 • (1 : Matrix m m ℝ)

/-- The variance `σ²_g d_i + σ²_e` of the `i`-th rotated error contrast at `θ = (σ²_g, σ²_e)`. -/
def contrastVar (d : r → ℝ) (θ : ℝ × ℝ) (i : r) : ℝ := θ.1 * d i + θ.2

/-- The spectral form of the GREML restricted log-likelihood, for contrast eigenvalues `d` and
rotated contrasts `w`:
`-(r/2) log 2π - (1/2) ∑ log λ_i(θ) - (1/2) ∑ w_i² / λ_i(θ)` with `λ_i(θ) = σ²_g d_i + σ²_e`. -/
noncomputable def spectralLogLik (d w : r → ℝ) (θ : ℝ × ℝ) : ℝ :=
  -(Fintype.card r / 2 * Real.log (2 * Real.pi)) - (∑ i, Real.log (contrastVar d θ i)) / 2 -
    (∑ i, w i ^ 2 / contrastVar d θ i) / 2

/-- `B` is an orthonormal error contrast for the design `X` that diagonalizes the relationship
matrix `K` on the contrast space, with eigenvalues `d`. -/
structure IsSpectralContrast (X : Matrix m k ℝ) (K : Matrix m m ℝ) (B : Matrix r m ℝ)
    (d : r → ℝ) : Prop where
  mul_eq_zero : B * X = 0
  mul_transpose : B * Bᵀ = 1
  card_add_card : Fintype.card r + Fintype.card k = Fintype.card m
  mul_mul_transpose : B * K * Bᵀ = diagonal d

omit [DecidableEq m] in
/-- A diagonalizing orthonormal contrast is an error contrast. -/
theorem IsSpectralContrast.isErrorContrast {X : Matrix m k ℝ} {K : Matrix m m ℝ}
    {B : Matrix r m ℝ} {d : r → ℝ} (hB : IsSpectralContrast X K B d) : IsErrorContrast X B where
  mul_eq_zero := hB.mul_eq_zero
  isUnit_mul_transpose := by rw [hB.mul_transpose]; exact isUnit_one
  card_add_card := hB.card_add_card

omit [Fintype r] in
/-- The contrast covariance of GREML is diagonal:
`B (σ²_g K + σ²_e I) Bᵀ = diag (σ²_g d + σ²_e)`. -/
theorem contrast_gremlCov {K : Matrix m m ℝ} {B : Matrix r m ℝ} {d : r → ℝ}
    (hBB : B * Bᵀ = 1) (hBK : B * K * Bᵀ = diagonal d) (θ : ℝ × ℝ) :
    B * gremlCov K θ * Bᵀ = diagonal (contrastVar d θ) := by
  have : B * gremlCov K θ * Bᵀ = θ.1 • (B * K * Bᵀ) + θ.2 • (B * Bᵀ) := by
    simp only [gremlCov, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one]
  rw [this, hBB, hBK]
  ext i j
  by_cases h : i = j
  · subst h; simp [contrastVar]
  · simp [diagonal_apply_ne _ h, one_apply_ne h]

private theorem inv_diagonal_of_ne {v : r → ℝ} (hv : ∀ i, v i ≠ 0) :
    (diagonal v)⁻¹ = diagonal fun i => (v i)⁻¹ := by
  refine inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst h; simp [hv i]
  · simp [diagonal_apply_ne _ h, one_apply_ne h]

omit [DecidableEq m] in
private theorem dotProduct_diagonal_inv (w v : r → ℝ) :
    w ⬝ᵥ diagonal (fun i => (v i)⁻¹) *ᵥ w = ∑ i, w i ^ 2 / v i := by
  simp only [dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_eq_mul_inv]; ring

/-- **GREML REML log-likelihood in spectral form.** For a diagonalizing orthonormal contrast and a
parameter at which every contrast variance `σ²_g d_i + σ²_e` is positive, the restricted
log-likelihood of `y` is `spectralLogLik d (B y) θ`. -/
theorem remlLogLik_gremlCov {K : Matrix m m ℝ} {B : Matrix r m ℝ} {d : r → ℝ}
    (hBB : B * Bᵀ = 1) (hBK : B * K * Bᵀ = diagonal d) {θ : ℝ × ℝ}
    (hθ : ∀ i, 0 < contrastVar d θ i) (y : m → ℝ) :
    remlLogLik B (gremlCov K θ) y = spectralLogLik d (B *ᵥ y) θ := by
  have hS : (B * gremlCov K θ * Bᵀ).PosDef := by
    rw [contrast_gremlCov hBB hBK]; exact posDef_diagonal_iff.mpr hθ
  rw [remlLogLik_eq hS, contrast_gremlCov hBB hBK, det_diagonal,
    Real.log_prod fun i _ => (hθ i).ne', inv_diagonal_of_ne fun i => (hθ i).ne',
    dotProduct_diagonal_inv, spectralLogLik]

omit [DecidableEq m] in
private theorem exists_orthogonal_diagonalize {S : Matrix r r ℝ} (hS : Sᵀ = S) :
    ∃ Q : Matrix r r ℝ, Q * Qᵀ = 1 ∧ Qᵀ * Q = 1 ∧
      Q * S * Qᵀ = diagonal (isHermitian_iff_isSymm.mpr hS).eigenvalues := by
  set hH : S.IsHermitian := isHermitian_iff_isSymm.mpr hS
  set U : Matrix r r ℝ := (hH.eigenvectorUnitary : Matrix r r ℝ)
  have hU := hH.eigenvectorUnitary.2
  have h1 : Uᵀ * U = 1 := by
    have := (mem_unitaryGroup_iff' (A := U)).mp hU
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
  have h2 : U * Uᵀ = 1 := by
    have := (mem_unitaryGroup_iff (A := U)).mp hU
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
  have hspec : S = U * diagonal hH.eigenvalues * Uᵀ := by
    have := hH.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, U] using this
  refine ⟨Uᵀ, by simpa using h1, by simpa using h2, ?_⟩
  conv_lhs => rw [hspec]
  rw [transpose_transpose]
  calc Uᵀ * (U * diagonal hH.eigenvalues * Uᵀ) * U
      = (Uᵀ * U) * diagonal hH.eigenvalues * (Uᵀ * U) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.one_mul, Matrix.mul_one]

omit [DecidableEq m] in
/-- **Every orthonormal error contrast rotates into a diagonalizing one.** If `A X = 0`,
`A Aᵀ = 1` and `card r + card k = card m`, and `K` is symmetric, there is an orthogonal `Q` such
that `Q A` diagonalizes `K` on the contrast space; the eigenvalues are nonnegative when `K` is
positive semidefinite. -/
theorem exists_isSpectralContrast {X : Matrix m k ℝ} {K : Matrix m m ℝ} (hK : Kᵀ = K)
    {A : Matrix r m ℝ} (hAX : A * X = 0) (hAA : A * Aᵀ = 1)
    (hcard : Fintype.card r + Fintype.card k = Fintype.card m) :
    ∃ (Q : Matrix r r ℝ) (d : r → ℝ), Q * Qᵀ = 1 ∧ Qᵀ * Q = 1 ∧
      IsSpectralContrast X K (Q * A) d ∧ (K.PosSemidef → ∀ i, 0 ≤ d i) := by
  have hS : (A * K * Aᵀ)ᵀ = A * K * Aᵀ := by
    rw [transpose_mul, transpose_mul, transpose_transpose, hK, Matrix.mul_assoc]
  obtain ⟨Q, hQ1, hQ2, hQS⟩ := exists_orthogonal_diagonalize hS
  refine ⟨Q, (isHermitian_iff_isSymm.mpr hS).eigenvalues, hQ1, hQ2, ⟨?_, ?_, hcard, ?_⟩,
    fun hKpsd i => ?_⟩
  · rw [Matrix.mul_assoc, hAX, Matrix.mul_zero]
  · rw [transpose_mul, show Q * A * (Aᵀ * Qᵀ) = Q * (A * Aᵀ) * Qᵀ by
      simp only [Matrix.mul_assoc], hAA, Matrix.mul_one, hQ1]
  · rw [← hQS, transpose_mul]; simp only [Matrix.mul_assoc]
  · have hpsd : (A * K * Aᵀ).PosSemidef := by
      simpa [conjTranspose_eq_transpose_of_trivial] using hKpsd.mul_mul_conjTranspose_same A
    exact hpsd.eigenvalues_nonneg i

/-- **The rotation does not change the criterion.** For an orthonormal contrast `A`, an orthogonal
`Q` with `Q A K (Q A)ᵀ = diag d`, and a parameter with every `σ²_g d_i + σ²_e > 0`, the REML
log-likelihood of `A` equals `spectralLogLik d (Q A y) θ`. -/
theorem remlLogLik_eq_spectralLogLik_of_orthogonal {K : Matrix m m ℝ} {A : Matrix r m ℝ}
    (hAA : A * Aᵀ = 1) {Q : Matrix r r ℝ} (hQ1 : Q * Qᵀ = 1) (hQ2 : Qᵀ * Q = 1) {d : r → ℝ}
    (hBK : Q * A * K * (Q * A)ᵀ = diagonal d) {θ : ℝ × ℝ} (hθ : ∀ i, 0 < contrastVar d θ i)
    (y : m → ℝ) :
    remlLogLik A (gremlCov K θ) y = spectralLogLik d ((Q * A) *ᵥ y) θ := by
  have hBB : Q * A * (Q * A)ᵀ = 1 := by
    rw [transpose_mul, show Q * A * (Aᵀ * Qᵀ) = Q * (A * Aᵀ) * Qᵀ by
      simp only [Matrix.mul_assoc], hAA, Matrix.mul_one, hQ1]
  have hAeq : A = Qᵀ * (Q * A) := by rw [← Matrix.mul_assoc, hQ2, Matrix.one_mul]
  have hS : (A * gremlCov K θ * Aᵀ).PosDef := by
    have h : A * gremlCov K θ * Aᵀ = Qᵀ * (Q * A * gremlCov K θ * (Q * A)ᵀ) * Qᵀᵀ := by
      conv_lhs => rw [hAeq]
      rw [transpose_mul]; simp only [Matrix.mul_assoc]
    rw [h, contrast_gremlCov hBB hBK]
    exact posDef_mul_mul_transpose (posDef_diagonal_iff.mpr hθ)
      (by rw [transpose_transpose, hQ2]; exact isUnit_one)
  have hdet : |Q.det| = 1 := by
    have h : Q.det * Q.det = 1 := by
      have := congrArg det hQ1
      rwa [det_mul, det_transpose, det_one] at this
    have h' : |Q.det| * |Q.det| = 1 := by rw [← abs_mul, h, abs_one]
    nlinarith [abs_nonneg Q.det]
  have hQu : IsUnit Q.det := by
    rw [isUnit_iff_ne_zero]; intro h0; rw [h0, abs_zero] at hdet; exact zero_ne_one hdet
  have := remlLogLik_mul_left hS hQu y
  rw [hdet, Real.log_one, sub_zero] at this
  rw [← this, remlLogLik_gremlCov hBB hBK hθ]

/-- The genetic relationship matrix `A = X Xᵀ / M` is positive semidefinite. -/
theorem posSemidef_grm {N M : ℕ} (X : Matrix (Fin N) (Fin M) ℝ) :
    (Matrix.of (GREML.grm X)).PosSemidef := by
  have h : Matrix.of (GREML.grm X) = (M : ℝ)⁻¹ • (X * Xᵀ) := by
    ext i j
    simp [GREML.grm, Matrix.mul_apply, div_eq_inv_mul]
  rw [h]
  have := posSemidef_self_mul_conjTranspose X
  rw [conjTranspose_eq_transpose_of_trivial] at this
  exact this.smul (by positivity)

/-! ### The REML score equations -/

/-- The REML score for `σ²_g`: `(1/2) ∑_i d_i (w_i² - λ_i) / λ_i²`. -/
noncomputable def scoreG (d w : r → ℝ) (θ : ℝ × ℝ) : ℝ :=
  (∑ i, d i * (w i ^ 2 - contrastVar d θ i) / contrastVar d θ i ^ 2) / 2

/-- The REML score for `σ²_e`: `(1/2) ∑_i (w_i² - λ_i) / λ_i²`. -/
noncomputable def scoreE (d w : r → ℝ) (θ : ℝ × ℝ) : ℝ :=
  (∑ i, (w i ^ 2 - contrastVar d θ i) / contrastVar d θ i ^ 2) / 2

omit [DecidableEq r] in
private theorem hasDerivAt_spectral_line (w : r → ℝ) (lam : ℝ → r → ℝ) (c : r → ℝ) (s : ℝ)
    (hlam : ∀ i, HasDerivAt (fun t => lam t i) (c i) s) (hpos : ∀ i, 0 < lam s i) :
    HasDerivAt (fun t => -(Fintype.card r / 2 * Real.log (2 * Real.pi)) -
        (∑ i, Real.log (lam t i)) / 2 - (∑ i, w i ^ 2 / lam t i) / 2)
      ((∑ i, c i * (w i ^ 2 - lam s i) / lam s i ^ 2) / 2) s := by
  have hlog : HasDerivAt (fun t => ∑ i, Real.log (lam t i)) (∑ i, c i / lam s i) s :=
    HasDerivAt.fun_sum fun i _ => (hlam i).log (hpos i).ne'
  have hq : HasDerivAt (fun t => ∑ i, w i ^ 2 / lam t i)
      (∑ i, -(w i ^ 2 * c i) / lam s i ^ 2) s :=
    HasDerivAt.fun_sum fun i _ => by
      convert ((hlam i).inv (hpos i).ne').const_mul (w i ^ 2) using 1
      · ext t; simp [div_eq_mul_inv]
      · ring
  convert ((hasDerivAt_const s _).sub (hlog.div_const 2)).sub (hq.div_const 2) using 1
  have h (i : r) : c i * (w i ^ 2 - lam s i) / lam s i ^ 2 =
      -(c i / lam s i) - (-(w i ^ 2 * c i) / lam s i ^ 2) := by
    have := (hpos i).ne'; field_simp; ring
  simp_rw [h, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

omit [DecidableEq r] in
/-- `∂ℓ/∂σ²_g = scoreG`, where every contrast variance is positive. -/
theorem hasDerivAt_spectralLogLik_fst {d : r → ℝ} (w : r → ℝ) {θ : ℝ × ℝ}
    (hθ : ∀ i, 0 < contrastVar d θ i) :
    HasDerivAt (fun s => spectralLogLik d w (s, θ.2)) (scoreG d w θ) θ.1 :=
  hasDerivAt_spectral_line w (fun s i => contrastVar d (s, θ.2) i) d θ.1
    (fun i => by simpa [contrastVar] using ((hasDerivAt_id θ.1).mul_const (d i)).add_const θ.2)
    hθ

omit [DecidableEq r] in
/-- `∂ℓ/∂σ²_e = scoreE`, where every contrast variance is positive. -/
theorem hasDerivAt_spectralLogLik_snd {d : r → ℝ} (w : r → ℝ) {θ : ℝ × ℝ}
    (hθ : ∀ i, 0 < contrastVar d θ i) :
    HasDerivAt (fun s => spectralLogLik d w (θ.1, s)) (scoreE d w θ) θ.2 := by
  have := hasDerivAt_spectral_line w (fun s i => contrastVar d (θ.1, s) i) (fun _ => 1) θ.2
    (fun i => by simpa [contrastVar] using (hasDerivAt_id θ.2).const_add (θ.1 * d i)) hθ
  simpa [scoreE, spectralLogLik] using this

omit [Fintype r] [DecidableEq r] in
/-- The region where every contrast variance is positive is open. -/
theorem isOpen_posContrastVar [Finite r] (d : r → ℝ) :
    IsOpen {θ : ℝ × ℝ | ∀ i, 0 < contrastVar d θ i} := by
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
    (by unfold contrastVar; fun_prop)

omit [DecidableEq r] in
/-- A local maximizer of the spectral criterion with positive contrast variances solves both score
equations. -/
theorem score_eq_zero_of_isLocalMax {d w : r → ℝ} {θ : ℝ × ℝ}
    (hθ : ∀ i, 0 < contrastVar d θ i) (hmax : IsLocalMax (spectralLogLik d w) θ) :
    scoreG d w θ = 0 ∧ scoreE d w θ = 0 := by
  refine ⟨?_, ?_⟩
  · have h : IsLocalMax (fun s => spectralLogLik d w (s, θ.2)) θ.1 :=
      hmax.comp_continuous (g := fun s => (s, θ.2)) (by fun_prop)
    exact h.hasDerivAt_eq_zero (hasDerivAt_spectralLogLik_fst w hθ)
  · have h : IsLocalMax (fun s => spectralLogLik d w (θ.1, s)) θ.2 :=
      hmax.comp_continuous (g := fun s => (θ.1, s)) (by fun_prop)
    exact h.hasDerivAt_eq_zero (hasDerivAt_spectralLogLik_snd w hθ)

/-- **REML score equations for GREML.** If `θ` is a local maximizer of the GREML restricted
log-likelihood `θ ↦ remlLogLik B (σ²_g K + σ²_e I) y` at which every contrast variance is
positive (an interior REML estimate), then both REML scores vanish at `θ`. -/
theorem score_eq_zero_of_isLocalMax_remlLogLik {K : Matrix m m ℝ} {B : Matrix r m ℝ}
    {d : r → ℝ} (hBB : B * Bᵀ = 1) (hBK : B * K * Bᵀ = diagonal d) {y : m → ℝ} {θ : ℝ × ℝ}
    (hθ : ∀ i, 0 < contrastVar d θ i)
    (hmax : IsLocalMax (fun φ => remlLogLik B (gremlCov K φ) y) θ) :
    scoreG d (B *ᵥ y) θ = 0 ∧ scoreE d (B *ᵥ y) θ = 0 := by
  refine score_eq_zero_of_isLocalMax hθ (hmax.congr ?_)
  filter_upwards [(isOpen_posContrastVar d).mem_nhds hθ] with φ hφ
  exact remlLogLik_gremlCov hBB hBK hφ y

/-- The REML projection `P = Bᵀ (B V Bᵀ)⁻¹ B` of an error contrast `B` at covariance `V`. -/
noncomputable def remlProj (B : Matrix r m ℝ) (V : Matrix m m ℝ) : Matrix m m ℝ :=
  Bᵀ * (B * V * Bᵀ)⁻¹ * B

omit [DecidableEq m] [DecidableEq r] in
private theorem dotProduct_transpose_mul_mul (B : Matrix r m ℝ) (N : Matrix r r ℝ)
    (y : m → ℝ) : y ⬝ᵥ (Bᵀ * N * B) *ᵥ y = (B *ᵥ y) ⬝ᵥ N *ᵥ (B *ᵥ y) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

private theorem remlProj_gremlCov {K : Matrix m m ℝ} {B : Matrix r m ℝ} {d : r → ℝ}
    (hBB : B * Bᵀ = 1) (hBK : B * K * Bᵀ = diagonal d) {θ : ℝ × ℝ}
    (hθ : ∀ i, 0 < contrastVar d θ i) :
    remlProj B (gremlCov K θ) = Bᵀ * diagonal (fun i => (contrastVar d θ i)⁻¹) * B := by
  rw [remlProj, contrast_gremlCov hBB hBK, inv_diagonal_of_ne fun i => (hθ i).ne']

/-- **The scores in GCTA's matrix form**: with `P = remlProj B (σ²_g K + σ²_e I)`,
`scoreG = (yᵀ P K P y - tr (P K)) / 2` and `scoreE = (yᵀ P P y - tr P) / 2`. -/
theorem score_eq_remlProj {K : Matrix m m ℝ} {B : Matrix r m ℝ} {d : r → ℝ}
    (hBB : B * Bᵀ = 1) (hBK : B * K * Bᵀ = diagonal d) {θ : ℝ × ℝ}
    (hθ : ∀ i, 0 < contrastVar d θ i) (y : m → ℝ) :
    scoreG d (B *ᵥ y) θ = (y ⬝ᵥ (remlProj B (gremlCov K θ) * K * remlProj B (gremlCov K θ)) *ᵥ y -
        (remlProj B (gremlCov K θ) * K).trace) / 2 ∧
      scoreE d (B *ᵥ y) θ = (y ⬝ᵥ (remlProj B (gremlCov K θ) * remlProj B (gremlCov K θ)) *ᵥ y -
        (remlProj B (gremlCov K θ)).trace) / 2 := by
  rw [remlProj_gremlCov hBB hBK hθ]
  set D := diagonal (fun i => (contrastVar d θ i)⁻¹)
  have h1 : Bᵀ * D * B * K * (Bᵀ * D * B) = Bᵀ * (D * (B * K * Bᵀ) * D) * B := by
    simp only [Matrix.mul_assoc]
  have h2 : Bᵀ * D * B * (Bᵀ * D * B) = Bᵀ * (D * (B * Bᵀ) * D) * B := by
    simp only [Matrix.mul_assoc]
  have h3 : (Bᵀ * D * B * K).trace = (D * (B * K * Bᵀ)).trace := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm]; simp only [Matrix.mul_assoc]
  have h4 : (Bᵀ * D * B).trace = (D * (B * Bᵀ)).trace := by
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [h1, h2, h3, h4, dotProduct_transpose_mul_mul, dotProduct_transpose_mul_mul, hBK, hBB,
    Matrix.mul_one, diagonal_mul_diagonal, diagonal_mul_diagonal,
    diagonal_mul_diagonal, trace_diagonal, trace_diagonal, scoreG, scoreE]
  simp only [dotProduct, mulVec_diagonal]
  constructor <;>
  · rw [← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (hθ i).ne'
    field_simp

/-- **GCTA's REML equations.** At an interior local maximizer `θ` of the GREML restricted
log-likelihood, with `P = remlProj B (σ²_g K + σ²_e I)`, `yᵀ P K P y = tr (P K)` and
`yᵀ P P y = tr P`. -/
theorem reml_equations_of_isLocalMax {K : Matrix m m ℝ} {B : Matrix r m ℝ} {d : r → ℝ}
    (hBB : B * Bᵀ = 1) (hBK : B * K * Bᵀ = diagonal d) {y : m → ℝ} {θ : ℝ × ℝ}
    (hθ : ∀ i, 0 < contrastVar d θ i)
    (hmax : IsLocalMax (fun φ => remlLogLik B (gremlCov K φ) y) θ) :
    y ⬝ᵥ (remlProj B (gremlCov K θ) * K * remlProj B (gremlCov K θ)) *ᵥ y =
        (remlProj B (gremlCov K θ) * K).trace ∧
      y ⬝ᵥ (remlProj B (gremlCov K θ) * remlProj B (gremlCov K θ)) *ᵥ y =
        (remlProj B (gremlCov K θ)).trace := by
  obtain ⟨hG, hE⟩ := score_eq_zero_of_isLocalMax_remlLogLik hBB hBK hθ hmax
  obtain ⟨hG', hE'⟩ := score_eq_remlProj hBB hBK hθ y
  rw [hG'] at hG; rw [hE'] at hE
  constructor <;> linarith

/-! ### Unbiasedness of the REML scores -/

section Unbiased

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [Fintype m] [DecidableEq m] [Fintype r] [DecidableEq r] in
private theorem integrable_integral_sq_of_hasLaw_gaussianReal {Z : Ω → ℝ} {v : NNReal}
    (hZ : HasLaw Z (gaussianReal 0 v) μ) :
    Integrable (fun ω => Z ω ^ 2) μ ∧ ∫ ω, Z ω ^ 2 ∂μ = v := by
  have hint : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
    simpa using (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  refine ⟨?_, ?_⟩
  · exact (integrable_map_measure (f := Z) (g := fun x : ℝ => x ^ 2)
      (by fun_prop) hZ.aemeasurable).mp (by rw [hZ.map_eq]; exact hint)
  · have h := hZ.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
    simp only [Function.comp_def] at h
    rw [h, ← variance_id_gaussianReal (μ := 0) (v := v),
      variance_eq_integral measurable_id.aemeasurable]
    simp [integral_id_gaussianReal]

/-- **Second moments of the rotated contrasts**: if `y ~ N(X β, σ²_g K + σ²_e I)` at `θ₀` with a
positive semidefinite covariance, then `w_i = (B y)_i` is square integrable with
`𝔼[w_i²] = σ²_{g,0} d_i + σ²_{e,0}`. -/
theorem integral_sq_contrast {X : Matrix m k ℝ} {K : Matrix m m ℝ} {B : Matrix r m ℝ}
    {d : r → ℝ} (hB : IsSpectralContrast X K B d) {θ₀ : ℝ × ℝ}
    (hV : (gremlCov K θ₀).PosSemidef) (β : k → ℝ) {y : Ω → EuclideanSpace ℝ m}
    (hy : HasLaw y (multivariateGaussian (toLp 2 (X *ᵥ β)) (gremlCov K θ₀)) μ) (i : r) :
    Integrable (fun ω => (B *ᵥ ofLp (y ω)) i ^ 2) μ ∧
      ∫ ω, (B *ᵥ ofLp (y ω)) i ^ 2 ∂μ = contrastVar d θ₀ i := by
  have hz := hasLaw_errorContrast hB.mul_eq_zero hV β hy
  have hS : (B * gremlCov K θ₀ * Bᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hV.mul_mul_conjTranspose_same B
  have hzi : HasLaw (fun ω => (B *ᵥ ofLp (y ω)) i)
      (gaussianReal 0 ((B * gremlCov K θ₀ * Bᵀ) i i).toNNReal) μ := by
    simpa using
      (measurePreserving_eval_multivariateGaussian (μ := 0) hS (i := i)).hasLaw.fun_comp hz
  obtain ⟨h1, h2⟩ := integrable_integral_sq_of_hasLaw_gaussianReal hzi
  refine ⟨h1, ?_⟩
  rw [h2, Real.coe_toNNReal _ hS.diag_nonneg, contrast_gremlCov hB.mul_transpose
    hB.mul_mul_transpose, diagonal_apply_eq]

set_option linter.unusedVariables false in
/-- **The REML score for `σ²_g` is unbiased**: at a true parameter `θ₀` with every contrast
variance positive, where `scoreG` is the derivative of the REML criterion, `𝔼[scoreG] = 0`. -/
theorem integral_scoreG [IsProbabilityMeasure μ] {X : Matrix m k ℝ} {K : Matrix m m ℝ}
    {B : Matrix r m ℝ} {d : r → ℝ} (hB : IsSpectralContrast X K B d) {θ₀ : ℝ × ℝ}
    (hV : (gremlCov K θ₀).PosSemidef) (hθ₀ : ∀ i, 0 < contrastVar d θ₀ i) (β : k → ℝ)
    {y : Ω → EuclideanSpace ℝ m}
    (hy : HasLaw y (multivariateGaussian (toLp 2 (X *ᵥ β)) (gremlCov K θ₀)) μ) :
    ∫ ω, scoreG d (B *ᵥ ofLp (y ω)) θ₀ ∂μ = 0 := by
  have hint : ∀ i ∈ Finset.univ, Integrable (fun ω => d i * ((B *ᵥ ofLp (y ω)) i ^ 2 -
      contrastVar d θ₀ i) / contrastVar d θ₀ i ^ 2) μ := fun i _ =>
    (((integral_sq_contrast hB hV β hy i).1.sub (integrable_const _)).const_mul _).div_const _
  simp only [scoreG]
  rw [integral_div, integral_finsetSum _ hint]
  refine div_eq_zero_iff.mpr (Or.inl (Finset.sum_eq_zero fun i _ => ?_))
  obtain ⟨h1, h2⟩ := integral_sq_contrast hB hV β hy i
  rw [integral_div, integral_const_mul, integral_sub h1 (integrable_const _), h2, integral_const]
  simp

set_option linter.unusedVariables false in
/-- **The REML score for `σ²_e` is unbiased**: at a true parameter `θ₀` with every contrast
variance positive, where `scoreE` is the derivative of the REML criterion, `𝔼[scoreE] = 0`. -/
theorem integral_scoreE [IsProbabilityMeasure μ] {X : Matrix m k ℝ} {K : Matrix m m ℝ}
    {B : Matrix r m ℝ} {d : r → ℝ} (hB : IsSpectralContrast X K B d) {θ₀ : ℝ × ℝ}
    (hV : (gremlCov K θ₀).PosSemidef) (hθ₀ : ∀ i, 0 < contrastVar d θ₀ i) (β : k → ℝ)
    {y : Ω → EuclideanSpace ℝ m}
    (hy : HasLaw y (multivariateGaussian (toLp 2 (X *ᵥ β)) (gremlCov K θ₀)) μ) :
    ∫ ω, scoreE d (B *ᵥ ofLp (y ω)) θ₀ ∂μ = 0 := by
  have hint : ∀ i ∈ Finset.univ, Integrable (fun ω => ((B *ᵥ ofLp (y ω)) i ^ 2 -
      contrastVar d θ₀ i) / contrastVar d θ₀ i ^ 2) μ := fun i _ =>
    ((integral_sq_contrast hB hV β hy i).1.sub (integrable_const _)).div_const _
  simp only [scoreE]
  rw [integral_div, integral_finsetSum _ hint]
  refine div_eq_zero_iff.mpr (Or.inl (Finset.sum_eq_zero fun i _ => ?_))
  obtain ⟨h1, h2⟩ := integral_sq_contrast hB hV β hy i
  rw [integral_div, integral_sub h1 (integrable_const _), h2, integral_const]
  simp

end Unbiased

/-! ### Closed-form REML estimator for two-level spectra -/

/-- The rotated contrasts whose eigenvalue is `a`. -/
noncomputable def classSet (d : r → ℝ) (a : ℝ) : Finset r := Finset.univ.filter fun i => d i = a

/-- The number of rotated contrasts whose eigenvalue is `a`. -/
noncomputable def groupCount (d : r → ℝ) (a : ℝ) : ℕ := (classSet d a).card

/-- The sum of `w_i²` over the rotated contrasts whose eigenvalue is `a`. -/
noncomputable def groupSS (d w : r → ℝ) (a : ℝ) : ℝ := ∑ i ∈ classSet d a, w i ^ 2

/-- The mean of `w_i²` over the rotated contrasts whose eigenvalue is `a` (`0` if there are
none). -/
noncomputable def groupMean (d w : r → ℝ) (a : ℝ) : ℝ := groupSS d w a / groupCount d a

/-- The closed-form REML estimate `(σ̂²_g, σ̂²_e)` for a spectrum with the two values `a ≠ b`:
`σ̂²_g = (m_a - m_b) / (a - b)` and `σ̂²_e = (a m_b - b m_a) / (a - b)`. -/
noncomputable def twoLevelREML (d w : r → ℝ) (a b : ℝ) : ℝ × ℝ :=
  ((groupMean d w a - groupMean d w b) / (a - b),
    (a * groupMean d w b - b * groupMean d w a) / (a - b))

omit [DecidableEq r] in
/-- At the closed-form estimate, the contrast variance of each class is its mean of `w_i²`. -/
theorem contrastVar_twoLevelREML {d w : r → ℝ} {a b : ℝ} (hab : a ≠ b) (i : r) :
    (d i = a → contrastVar d (twoLevelREML d w a b) i = groupMean d w a) ∧
      (d i = b → contrastVar d (twoLevelREML d w a b) i = groupMean d w b) := by
  have h : a - b ≠ 0 := sub_ne_zero.mpr hab
  constructor <;> intro hi <;> simp only [contrastVar, twoLevelREML, hi] <;> field_simp <;> ring

private theorem key_ineq {n S x : ℝ} (hn : 0 < n) (hS : 0 < S) (hx : 0 < x) :
    n * Real.log (S / n) + n ≤ n * Real.log x + S / x ∧
      (n * Real.log (S / n) + n = n * Real.log x + S / x → x = S / n) := by
  have ht : 0 < S / n / x := by positivity
  have hlog : Real.log (S / n / x) = Real.log (S / n) - Real.log x :=
    Real.log_div (by positivity) hx.ne'
  have hid : n * (S / n / x - 1) = S / x - n := by field_simp
  refine ⟨?_, fun heq => ?_⟩
  · have := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos ht) hn.le
    rw [hlog, hid] at this
    linarith
  · by_contra hne
    have hne' : S / n / x ≠ 1 := by
      intro h; apply hne; field_simp at h; rw [h, mul_div_cancel_left₀ _ hn.ne']
    have := mul_lt_mul_of_pos_left (Real.log_lt_sub_one_of_pos ht hne') hn
    rw [hlog, hid] at this
    linarith

omit [DecidableEq r] in
private theorem sum_class (d w : r → ℝ) (a : ℝ) (θ : ℝ × ℝ) :
    ∑ i ∈ classSet d a, (Real.log (contrastVar d θ i) + w i ^ 2 / contrastVar d θ i) =
      groupCount d a * Real.log (θ.1 * a + θ.2) + groupSS d w a / (θ.1 * a + θ.2) := by
  rw [Finset.sum_add_distrib, groupSS, groupCount, Finset.sum_div]
  have h1 : ∀ i ∈ classSet d a, contrastVar d θ i = θ.1 * a + θ.2 := by
    intro i hi; simp only [classSet, Finset.mem_filter] at hi; simp [contrastVar, hi.2]
  rw [Finset.sum_congr rfl (fun i hi => (by rw [h1 i hi] :
      Real.log (contrastVar d θ i) = Real.log (θ.1 * a + θ.2))),
    Finset.sum_congr rfl (fun i hi => (by rw [h1 i hi] :
      w i ^ 2 / contrastVar d θ i = w i ^ 2 / (θ.1 * a + θ.2))), Finset.sum_const,
    nsmul_eq_mul]

omit [DecidableEq r] in
private theorem sum_split {d : r → ℝ} {a b : ℝ} (hab : a ≠ b) (hd : ∀ i, d i = a ∨ d i = b)
    (f : r → ℝ) : ∑ i, f i = ∑ i ∈ classSet d a, f i + ∑ i ∈ classSet d b, f i := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => d i = a)]
  congr 1
  congr 1; ext i
  simp only [classSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hd i with h | h <;> simp [h, hab, hab.symm]

omit [DecidableEq r] in
private theorem groupCount_pos_of_groupMean_pos {d w : r → ℝ} {a : ℝ}
    (h : 0 < groupMean d w a) : 0 < (groupCount d a : ℝ) := by
  rcases (Nat.cast_nonneg (α := ℝ) (groupCount d a)).lt_or_eq with h' | h'
  · exact h'
  · rw [groupMean, ← h', div_zero] at h; exact absurd h (lt_irrefl 0)

omit [DecidableEq r] in
private theorem exists_of_groupCount_pos {d : r → ℝ} {a : ℝ} (h : 0 < (groupCount d a : ℝ)) :
    ∃ i, d i = a := by
  by_contra! hne
  have : groupCount d a = 0 := by simp [groupCount, classSet, hne]
  rw [this] at h; simp at h

omit [DecidableEq r] in
/-- **The closed-form estimate maximizes the spectral REML criterion.** If the spectrum takes only
the values `a ≠ b` and both class means of `w_i²` are positive, then `twoLevelREML d w a b`
maximizes `spectralLogLik d w` over the region where every contrast variance is positive, and it
is the only maximizer there. -/
theorem isMaxOn_spectralLogLik_twoLevelREML {d w : r → ℝ} {a b : ℝ} (hab : a ≠ b)
    (hd : ∀ i, d i = a ∨ d i = b) (ha : 0 < groupMean d w a) (hb : 0 < groupMean d w b)
    {θ : ℝ × ℝ} (hθ : ∀ i, 0 < contrastVar d θ i) :
    spectralLogLik d w θ ≤ spectralLogLik d w (twoLevelREML d w a b) ∧
      (spectralLogLik d w θ = spectralLogLik d w (twoLevelREML d w a b) →
        θ = twoLevelREML d w a b) := by
  have hna := groupCount_pos_of_groupMean_pos ha
  have hnb := groupCount_pos_of_groupMean_pos hb
  have hSa : 0 < groupSS d w a := by
    have : groupSS d w a = groupMean d w a * groupCount d a := by
      rw [groupMean]; field_simp
    rw [this]; positivity
  have hSb : 0 < groupSS d w b := by
    have : groupSS d w b = groupMean d w b * groupCount d b := by
      rw [groupMean]; field_simp
    rw [this]; positivity
  obtain ⟨ia, hia⟩ := exists_of_groupCount_pos hna
  obtain ⟨ib, hib⟩ := exists_of_groupCount_pos hnb
  have hxa : 0 < θ.1 * a + θ.2 := by simpa [contrastVar, hia] using hθ ia
  have hxb : 0 < θ.1 * b + θ.2 := by simpa [contrastVar, hib] using hθ ib
  set θh := twoLevelREML d w a b
  have hθha : θh.1 * a + θh.2 = groupMean d w a := by
    simpa [contrastVar, hia] using (contrastVar_twoLevelREML (w := w) hab ia).1 hia
  have hθhb : θh.1 * b + θh.2 = groupMean d w b := by
    simpa [contrastVar, hib] using (contrastVar_twoLevelREML (w := w) hab ib).2 hib
  have hma : groupMean d w a = groupSS d w a / groupCount d a := rfl
  have hmb : groupMean d w b = groupSS d w b / groupCount d b := rfl
  obtain ⟨hA, hA'⟩ := key_ineq hna hSa hxa
  obtain ⟨hB, hB'⟩ := key_ineq hnb hSb hxb
  have hF : ∀ φ : ℝ × ℝ, spectralLogLik d w φ =
      -(Fintype.card r / 2 * Real.log (2 * Real.pi)) -
      (groupCount d a * Real.log (φ.1 * a + φ.2) + groupSS d w a / (φ.1 * a + φ.2) +
        (groupCount d b * Real.log (φ.1 * b + φ.2) + groupSS d w b / (φ.1 * b + φ.2))) / 2 := by
    intro φ
    rw [spectralLogLik, ← sum_class, ← sum_class, ← sum_split hab hd, Finset.sum_add_distrib]
    ring
  have hval : groupSS d w a / groupMean d w a = groupCount d a ∧
      groupSS d w b / groupMean d w b = groupCount d b := by
    constructor
    · rw [hma]; field_simp
    · rw [hmb]; field_simp
  rw [hF θ, hF θh, hθha, hθhb, hval.1, hval.2]
  rw [← hma] at hA hA'; rw [← hmb] at hB hB'
  refine ⟨by linarith, fun heq => ?_⟩
  have h1 := hA' (by linarith)
  have h2 := hB' (by linarith)
  rw [← hθha] at h1; rw [← hθhb] at h2
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hfst : θ.1 = θh.1 := by
    have : (θ.1 - θh.1) * (a - b) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hab'
  exact Prod.ext hfst (by rw [hfst] at h1; linarith)

/-- **Closed-form GREML REML estimator for two-level spectra.** For a diagonalizing orthonormal
contrast whose eigenvalues take only the values `a ≠ b`, if both class means of `(B y)_i²` are
positive, then `twoLevelREML d (B y) a b` maximizes the GREML restricted log-likelihood over the
region where the contrast covariance is positive definite, and is its unique maximizer there. -/
theorem isMaxOn_remlLogLik_twoLevelREML {K : Matrix m m ℝ} {B : Matrix r m ℝ} {d : r → ℝ}
    (hBB : B * Bᵀ = 1) (hBK : B * K * Bᵀ = diagonal d) {y : m → ℝ} {a b : ℝ} (hab : a ≠ b)
    (hd : ∀ i, d i = a ∨ d i = b) (ha : 0 < groupMean d (B *ᵥ y) a)
    (hb : 0 < groupMean d (B *ᵥ y) b) :
    twoLevelREML d (B *ᵥ y) a b ∈ {θ : ℝ × ℝ | ∀ i, 0 < contrastVar d θ i} ∧
      IsMaxOn (fun θ => remlLogLik B (gremlCov K θ) y) {θ | ∀ i, 0 < contrastVar d θ i}
        (twoLevelREML d (B *ᵥ y) a b) ∧
      ∀ θ ∈ {θ : ℝ × ℝ | ∀ i, 0 < contrastVar d θ i},
        remlLogLik B (gremlCov K θ) y = remlLogLik B (gremlCov K (twoLevelREML d (B *ᵥ y) a b)) y →
          θ = twoLevelREML d (B *ᵥ y) a b := by
  have hmem : ∀ i, 0 < contrastVar d (twoLevelREML d (B *ᵥ y) a b) i := by
    intro i
    rcases hd i with h | h
    · rw [(contrastVar_twoLevelREML hab i).1 h]; exact ha
    · rw [(contrastVar_twoLevelREML hab i).2 h]; exact hb
  refine ⟨hmem, fun θ hθ => ?_, fun θ hθ heq => ?_⟩
  · simp only [Set.mem_ofPred_eq]
    rw [remlLogLik_gremlCov hBB hBK hθ, remlLogLik_gremlCov hBB hBK hmem]
    exact (isMaxOn_spectralLogLik_twoLevelREML hab hd ha hb hθ).1
  · rw [remlLogLik_gremlCov hBB hBK hθ, remlLogLik_gremlCov hBB hBK hmem] at heq
    exact (isMaxOn_spectralLogLik_twoLevelREML hab hd ha hb hθ).2 heq

section Unbiased

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

private theorem integral_groupMean [IsProbabilityMeasure μ] {X : Matrix m k ℝ}
    {K : Matrix m m ℝ} {B : Matrix r m ℝ} {d : r → ℝ} (hB : IsSpectralContrast X K B d)
    {θ₀ : ℝ × ℝ} (hV : (gremlCov K θ₀).PosSemidef) (β : k → ℝ) {y : Ω → EuclideanSpace ℝ m}
    (hy : HasLaw y (multivariateGaussian (toLp 2 (X *ᵥ β)) (gremlCov K θ₀)) μ) {a : ℝ}
    (ha : ∃ i, d i = a) :
    Integrable (fun ω => groupMean d (B *ᵥ ofLp (y ω)) a) μ ∧
      ∫ ω, groupMean d (B *ᵥ ofLp (y ω)) a ∂μ = θ₀.1 * a + θ₀.2 := by
  obtain ⟨i₀, hi₀⟩ := ha
  have hn : (groupCount d a : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, groupCount, ← Nat.pos_iff_ne_zero, Finset.card_pos]
    exact ⟨i₀, by simp [classSet, hi₀]⟩
  have hint : ∀ i ∈ classSet d a, Integrable (fun ω => (B *ᵥ ofLp (y ω)) i ^ 2) μ :=
    fun i _ => (integral_sq_contrast hB hV β hy i).1
  refine ⟨(integrable_finsetSum _ hint).div_const _, ?_⟩
  simp only [groupMean, groupSS]
  rw [integral_div, integral_finsetSum _ hint]
  rw [Finset.sum_congr rfl fun i hi => (integral_sq_contrast hB hV β hy i).2]
  have h1 : ∀ i ∈ classSet d a, contrastVar d θ₀ i = θ₀.1 * a + θ₀.2 := by
    intro i hi; simp only [classSet, Finset.mem_filter] at hi; simp [contrastVar, hi.2]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, groupCount]
  rw [groupCount] at hn
  field_simp

/-- **The closed-form REML estimator is unbiased**: if `y ~ N(X β, σ²_g K + σ²_e I)` at `θ₀` and
the spectrum takes the two values `a ≠ b`, each at least once, then
`𝔼[σ̂²_g] = σ²_{g,0}` and `𝔼[σ̂²_e] = σ²_{e,0}`. -/
theorem integral_twoLevelREML [IsProbabilityMeasure μ] {X : Matrix m k ℝ} {K : Matrix m m ℝ}
    {B : Matrix r m ℝ} {d : r → ℝ} (hB : IsSpectralContrast X K B d) {θ₀ : ℝ × ℝ}
    (hV : (gremlCov K θ₀).PosSemidef) (β : k → ℝ) {y : Ω → EuclideanSpace ℝ m}
    (hy : HasLaw y (multivariateGaussian (toLp 2 (X *ᵥ β)) (gremlCov K θ₀)) μ) {a b : ℝ}
    (hab : a ≠ b) (ha : ∃ i, d i = a) (hb : ∃ i, d i = b) :
    ∫ ω, (twoLevelREML d (B *ᵥ ofLp (y ω)) a b).1 ∂μ = θ₀.1 ∧
      ∫ ω, (twoLevelREML d (B *ᵥ ofLp (y ω)) a b).2 ∂μ = θ₀.2 := by
  obtain ⟨hia, hEa⟩ := integral_groupMean hB hV β hy ha
  obtain ⟨hib, hEb⟩ := integral_groupMean hB hV β hy hb
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  simp only [twoLevelREML]
  constructor
  · rw [integral_div, integral_sub hia hib, hEa, hEb]
    field_simp; ring
  · rw [integral_div, integral_sub (hib.const_mul a) (hia.const_mul b), integral_const_mul,
      integral_const_mul, hEa, hEb]
    field_simp; ring

end Unbiased

end MathlibExt.Biology.StatisticalGenetics.GREMLREML
