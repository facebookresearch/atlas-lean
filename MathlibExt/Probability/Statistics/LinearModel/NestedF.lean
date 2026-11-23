/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.Sampling
public import MathlibExt.Probability.Distributions.SnedecorF
import MathlibExt.Probability.Statistics.ANOVA.NestedProjector

/-!
# Exact `F` law for a nested-model restriction (Atlas ST04.T04)

Write `U = col(X)` for the unrestricted design and `R = col(X₀)` for the
restricted design, with `R ≤ U`. The restricted and unrestricted residual
sums of squares are `RSS_R = ‖y - X₀ γ̂‖²` and `RSS_U = ‖y - X β̂‖²`. The
nested-model statistic is
`F = ((RSS_R - RSS_U) / q) / (RSS_U / (n - p))` with `q = p - p₀`.

Under `H₀` (the mean `X β` lies in `R`), `RSS_R - RSS_U = ‖P_{Rᗮ ⊓ U} y‖²`
and `RSS_U = ‖P_{Uᗮ} y‖²` are `σ²` times squared norms of projections of
the standardized errors onto orthogonal subspaces, hence independent
chi-squares with `q` and `n - p` degrees of freedom; the ratio law is
`snedecorFMeasure q (n - p)`. The closed-form `F` density is NOT proved
here. This specializes Cochran's theorem; it does not reprove it, and it
does not reprove the general linear-hypothesis `F` law
`hasLaw_fStatistic` (that theorem is for a hypothesis `C β = c`, not for
the RSS-difference form).
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory

namespace MathlibExt.Probability.Statistics.LinearModel

/-- The residual sum of squares `‖y - X β̂‖²` of the design `X` at `y`. -/
noncomputable def rssDesign {m k : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] (X : Matrix m k ℝ) (y : m → ℝ) : ℝ :=
  (y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y)

/-- The nested-model `F` statistic `((RSS_R - RSS_U) / q) / (RSS_U / (n - p))`
for restricted design `X₀` and unrestricted design `X`. -/
noncomputable def nestedFStatistic {m k k₀ : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] [Fintype k₀] [DecidableEq k₀]
    (X : Matrix m k ℝ) (X₀ : Matrix m k₀ ℝ) (y : m → ℝ) : ℝ :=
  ((rssDesign X₀ y - rssDesign X y) /
      ((Fintype.card k - Fintype.card k₀ : ℕ) : ℝ)) /
    (rssDesign X y / ((Fintype.card m - Fintype.card k : ℕ) : ℝ))

/-- The residual sum of squares of a full-rank design is the squared norm
of the projection of `y` onto the orthogonal complement of the column
space. -/
theorem rssDesign_eq_norm_sq_starProjection {m k : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] {X : Matrix m k ℝ} (hX : IsUnit (Xᵀ * X))
    (y : m → ℝ) :
    rssDesign X y =
      ‖(LinearMap.range (Matrix.toEuclideanLin X))ᗮ.starProjection
        (WithLp.toLp 2 y)‖ ^ 2 := by
  have hXM : Xᵀ * residualMatrix X = 0 := by
    have h1 : (residualMatrix X * X)ᵀ = (0 : Matrix m k ℝ)ᵀ := by
      rw [residualMatrix_mul hX]
    rw [Matrix.transpose_mul, residualMatrix_transpose, Matrix.transpose_zero] at h1
    exact h1
  have hXr : Xᵀ *ᵥ (residualMatrix X *ᵥ y) = 0 := by
    rw [Matrix.mulVec_mulVec, hXM, Matrix.zero_mulVec]
  have hmem1 : WithLp.toLp 2 (residualMatrix X *ᵥ y)
      ∈ (LinearMap.range (Matrix.toEuclideanLin X))ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hu
    have hrX : (residualMatrix X *ᵥ y) ᵥ* X = Xᵀ *ᵥ (residualMatrix X *ᵥ y) :=
      (Matrix.mulVec_transpose X _).symm
    have hdot : (X *ᵥ w.ofLp) ⬝ᵥ (residualMatrix X *ᵥ y) = 0 := by
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, hrX, hXr]
      simp [dotProduct]
    rw [← hw, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
    simp only
    rw [star_trivial]
    exact hdot
  have hyr : y - residualMatrix X *ᵥ y = X *ᵥ olsEstimator X y := by
    rw [← sub_mulVec_olsEstimator X y]
    abel
  have hmem2 : WithLp.toLp 2 y - WithLp.toLp 2 (residualMatrix X *ᵥ y)
      ∈ (LinearMap.range (Matrix.toEuclideanLin X))ᗮᗮ := by
    have h1 : WithLp.toLp 2 y - WithLp.toLp 2 (residualMatrix X *ᵥ y)
        = Matrix.toEuclideanLin X (WithLp.toLp 2 (olsEstimator X y)) := by
      rw [← WithLp.toLp_sub, hyr, Matrix.toLpLin_toLp, Matrix.toLin'_apply]
    rw [h1, Submodule.mem_orthogonal']
    intro u hu
    exact Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self _ _) hu
  have hproj : (LinearMap.range (Matrix.toEuclideanLin X))ᗮ.starProjection
      (WithLp.toLp 2 y) = WithLp.toLp 2 (residualMatrix X *ᵥ y) :=
    Submodule.eq_starProjection_of_mem_orthogonal hmem1 hmem2
  have hnorm : (residualMatrix X *ᵥ y) ⬝ᵥ (residualMatrix X *ᵥ y)
      = ‖WithLp.toLp 2 (residualMatrix X *ᵥ y)‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct, pow_two]
  unfold rssDesign
  rw [sub_mulVec_olsEstimator, hnorm, hproj]

/-- The difference of nested residual sums of squares is the squared norm
of the projection onto `Rᗮ ⊓ U`, the orthogonal complement of `R` inside
`U`. -/
theorem rssDesign_sub_eq_norm_sq_starProjection {m k k₀ : Type*} [Fintype m]
    [DecidableEq m] [Fintype k] [DecidableEq k] [Fintype k₀] [DecidableEq k₀]
    {X : Matrix m k ℝ} {X₀ : Matrix m k₀ ℝ} (hX : IsUnit (Xᵀ * X))
    (hX₀ : IsUnit (X₀ᵀ * X₀))
    (hsub : LinearMap.range (Matrix.toEuclideanLin X₀) ≤
      LinearMap.range (Matrix.toEuclideanLin X)) (y : m → ℝ) :
    rssDesign X₀ y - rssDesign X y =
      ‖((LinearMap.range (Matrix.toEuclideanLin X₀))ᗮ ⊓
        LinearMap.range (Matrix.toEuclideanLin X)).starProjection
        (WithLp.toLp 2 y)‖ ^ 2 := by
  have h1 := rssDesign_eq_norm_sq_starProjection hX y
  have h0 := rssDesign_eq_norm_sq_starProjection hX₀ y
  have hle : (LinearMap.range (Matrix.toEuclideanLin X))ᗮ
      ≤ (LinearMap.range (Matrix.toEuclideanLin X₀))ᗮ :=
    Submodule.orthogonal_le hsub
  have hsplit := sum_sq_split_nested _ _ hle (WithLp.toLp 2 y)
  have hincr := increment_projection_eq _ _ hle (WithLp.toLp 2 y)
  rw [Submodule.orthogonal_orthogonal] at hincr
  rw [h0, h1, hincr]
  linear_combination hsplit

/-- A full-rank design's Euclidean map is injective, via the OLS left inverse. -/
private theorem injective_toEuclideanLin_of_isUnit {m k : Type*} [Fintype m]
    [Fintype k] [DecidableEq k] {X : Matrix m k ℝ} (hX : IsUnit (Xᵀ * X)) :
    Function.Injective (Matrix.toEuclideanLin X) := by
  classical
  intro u v huv
  have h2 := congrArg WithLp.ofLp huv
  rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
    WithLp.ofLp_toLp] at h2
  have h3 : olsMatrix X *ᵥ (X *ᵥ u.ofLp) = olsMatrix X *ᵥ (X *ᵥ v.ofLp) := by
    rw [h2]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, olsMatrix_mul_self hX,
    Matrix.one_mulVec, Matrix.one_mulVec] at h3
  have h4 := congrArg (WithLp.toLp 2) h3
  rwa [WithLp.toLp_ofLp, WithLp.toLp_ofLp] at h4

/-- **Exact `F` law of the nested-model statistic**: in `y = X β + ε` with
full-rank `X` and `X₀`, `R = col(X₀) ≤ U = col(X)`, `p₀ < p < n`,
`σ > 0`, `σ⁻¹ ε` standard Gaussian, and under `H₀` (the mean `X β` lies in
`R`, witnessed by `X β = X₀ β₀`), the nested-model statistic has
Snedecor's `F` law with `(p - p₀, n - p)` degrees of freedom. -/
theorem hasLaw_nestedFStatistic {m k k₀ : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] [Fintype k₀] [DecidableEq k₀]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Matrix m k ℝ} {X₀ : Matrix m k₀ ℝ} (hX : IsUnit (Xᵀ * X))
    (hX₀ : IsUnit (X₀ᵀ * X₀))
    (hsub : LinearMap.range (Matrix.toEuclideanLin X₀) ≤
      LinearMap.range (Matrix.toEuclideanLin X))
    (hk₀k : Fintype.card k₀ < Fintype.card k) (hkm : Fintype.card k < Fintype.card m)
    (β : k → ℝ) {β₀ : k₀ → ℝ} (hβ : X *ᵥ β = X₀ *ᵥ β₀)
    {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    HasLaw (fun ω => nestedFStatistic X X₀ (X *ᵥ β + ε ω))
      (snedecorFMeasure (Fintype.card k - Fintype.card k₀)
        (Fintype.card m - Fintype.card k)) μ := by
  have hσ0 : σ ≠ 0 := by linarith
  have hS : σ ^ 2 ≠ 0 := by nlinarith [hσ]
  have hq : ((Fintype.card k - Fintype.card k₀ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show Fintype.card k - Fintype.card k₀ ≠ 0 from by omega)
  have hQ : ((Fintype.card m - Fintype.card k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show Fintype.card m - Fintype.card k ≠ 0 from by omega)
  have hcomm : ∀ (a t : ℝ), t ≠ 0 → (a / σ ^ 2) / t = (a / t) / σ ^ 2 := by
    intro a t ht
    field_simp [hS, ht]
  have hcancel : ∀ (a b : ℝ), (a / ((Fintype.card k - Fintype.card k₀ : ℕ) : ℝ)) /
      (b / ((Fintype.card m - Fintype.card k : ℕ) : ℝ))
      = ((a / σ ^ 2) / ((Fintype.card k - Fintype.card k₀ : ℕ) : ℝ)) /
        ((b / σ ^ 2) / ((Fintype.card m - Fintype.card k : ℕ) : ℝ)) := by
    intro a b
    rw [hcomm a _ hq, hcomm b _ hQ]
    exact (div_div_div_cancel_right₀ hS _ _).symm
  have hmeas : Measurable (WithLp.toLp 2 : (m → ℝ) → EuclideanSpace ℝ m) := by
    fun_prop
  have hmap : HasLaw (WithLp.toLp 2 : (m → ℝ) → EuclideanSpace ℝ m)
      (stdGaussian (EuclideanSpace ℝ m)) (Measure.pi fun _ : m => gaussianReal 0 1) :=
    ⟨hmeas.aemeasurable, map_pi_eq_stdGaussian⟩
  have hZ : HasLaw (fun ω => WithLp.toLp 2 (σ⁻¹ • ε ω))
      (stdGaussian (EuclideanSpace ℝ m)) μ :=
    HasLaw.fun_comp hmap hε
  have := hε.isProbabilityMeasure
  have hm : WithLp.toLp 2 (X₀ *ᵥ β₀)
      ∈ LinearMap.range (Matrix.toEuclideanLin X₀) := by
    have harg : Matrix.toEuclideanLin X₀ (WithLp.toLp 2 β₀)
        = WithLp.toLp 2 (X₀ *ᵥ β₀) := by
      rw [Matrix.toLpLin_toLp, Matrix.toLin'_apply]
    rw [← harg]
    exact LinearMap.mem_range_self _ _
  have hid : ∀ ω, WithLp.toLp 2 (X *ᵥ β + ε ω) = WithLp.toLp 2 (X₀ *ᵥ β₀) +
      σ • WithLp.toLp 2 (σ⁻¹ • ε ω) := by
    intro ω
    rw [hβ, WithLp.toLp_add]
    congr 1
    rw [← WithLp.toLp_smul, smul_inv_smul₀ hσ0]
  have hfinU : Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin X))
      = Fintype.card k := by
    rw [LinearMap.finrank_range_of_inj (injective_toEuclideanLin_of_isUnit hX),
      finrank_euclideanSpace]
  have hfinR : Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin X₀))
      = Fintype.card k₀ := by
    rw [LinearMap.finrank_range_of_inj (injective_toEuclideanLin_of_isUnit hX₀),
      finrank_euclideanSpace]
  have hqfin : 0 < Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin X)) -
      Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin X₀)) := by
    rw [hfinU, hfinR]
    omega
  have hresfin : 0 < Module.finrank ℝ (EuclideanSpace ℝ m) -
      Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin X)) := by
    rw [finrank_euclideanSpace, hfinU]
    omega
  have hV₁ : HasLaw (fun ω => ‖(LinearMap.range (Matrix.toEuclideanLin X) ⊓
      (LinearMap.range (Matrix.toEuclideanLin X₀))ᗮ).starProjection
      (WithLp.toLp 2 (X₀ *ᵥ β₀) + σ • WithLp.toLp 2 (σ⁻¹ • ε ω))‖ ^ 2 / σ ^ 2)
      (chiSquareMeasure (Fintype.card k - Fintype.card k₀)) μ := by
    have h := hasLaw_increment_chiSq (LinearMap.range (Matrix.toEuclideanLin X₀))
      (LinearMap.range (Matrix.toEuclideanLin X)) hsub hZ hσ hm hqfin
    rwa [hfinU, hfinR] at h
  have hV₂ : HasLaw (fun ω => ‖(LinearMap.range (Matrix.toEuclideanLin X))ᗮ.starProjection
      (WithLp.toLp 2 (X₀ *ᵥ β₀) + σ • WithLp.toLp 2 (σ⁻¹ • ε ω))‖ ^ 2 / σ ^ 2)
      (chiSquareMeasure (Fintype.card m - Fintype.card k)) μ := by
    have h := hasLaw_residual_chiSq (LinearMap.range (Matrix.toEuclideanLin X₀))
      (LinearMap.range (Matrix.toEuclideanLin X)) hsub hZ hσ hm hresfin
    rwa [finrank_euclideanSpace, hfinU] at h
  have hindep := indepFun_increment_residual
    (LinearMap.range (Matrix.toEuclideanLin X₀))
    (LinearMap.range (Matrix.toEuclideanLin X)) hsub hZ hσ hm
  have h₁ : 0 < Fintype.card k - Fintype.card k₀ := by omega
  have h₂ : 0 < Fintype.card m - Fintype.card k := by omega
  have hmapF := map_div_chiSquare_eq_snedecorF h₁ h₂ hV₁ hV₂ hindep
  have hstat : ∀ ω, nestedFStatistic X X₀ (X *ᵥ β + ε ω)
      = ((‖(LinearMap.range (Matrix.toEuclideanLin X) ⊓
        (LinearMap.range (Matrix.toEuclideanLin X₀))ᗮ).starProjection
        (WithLp.toLp 2 (X₀ *ᵥ β₀) + σ • WithLp.toLp 2 (σ⁻¹ • ε ω))‖ ^ 2 / σ ^ 2) /
        ((Fintype.card k - Fintype.card k₀ : ℕ) : ℝ)) /
        (((‖(LinearMap.range (Matrix.toEuclideanLin X))ᗮ.starProjection
        (WithLp.toLp 2 (X₀ *ᵥ β₀) + σ • WithLp.toLp 2 (σ⁻¹ • ε ω))‖ ^ 2 / σ ^ 2)) /
        ((Fintype.card m - Fintype.card k : ℕ) : ℝ)) := by
    intro ω
    have eU : rssDesign X (X *ᵥ β + ε ω)
        = ‖(LinearMap.range (Matrix.toEuclideanLin X))ᗮ.starProjection
          (WithLp.toLp 2 (X₀ *ᵥ β₀) + σ • WithLp.toLp 2 (σ⁻¹ • ε ω))‖ ^ 2 := by
      rw [rssDesign_eq_norm_sq_starProjection hX, hid]
    have eR : rssDesign X₀ (X *ᵥ β + ε ω) - rssDesign X (X *ᵥ β + ε ω)
        = ‖(LinearMap.range (Matrix.toEuclideanLin X) ⊓
          (LinearMap.range (Matrix.toEuclideanLin X₀))ᗮ).starProjection
          (WithLp.toLp 2 (X₀ *ᵥ β₀) + σ • WithLp.toLp 2 (σ⁻¹ • ε ω))‖ ^ 2 := by
      rw [rssDesign_sub_eq_norm_sq_starProjection hX hX₀ hsub, hid]
      simp only [inf_comm]
    unfold nestedFStatistic
    rw [eR, eU]
    exact hcancel _ _
  have hfun : (fun ω => nestedFStatistic X X₀ (X *ᵥ β + ε ω))
      = (fun ω => ((‖(LinearMap.range (Matrix.toEuclideanLin X) ⊓
        (LinearMap.range (Matrix.toEuclideanLin X₀))ᗮ).starProjection
        (WithLp.toLp 2 (X₀ *ᵥ β₀) + σ • WithLp.toLp 2 (σ⁻¹ • ε ω))‖ ^ 2 / σ ^ 2) /
        ((Fintype.card k - Fintype.card k₀ : ℕ) : ℝ)) /
        (((‖(LinearMap.range (Matrix.toEuclideanLin X))ᗮ.starProjection
        (WithLp.toLp 2 (X₀ *ᵥ β₀) + σ • WithLp.toLp 2 (σ⁻¹ • ε ω))‖ ^ 2 / σ ^ 2)) /
        ((Fintype.card m - Fintype.card k : ℕ) : ℝ))) :=
    funext hstat
  rw [hfun]
  exact ⟨(hV₁.aemeasurable.div_const _).div (hV₂.aemeasurable.div_const _), hmapF⟩

end MathlibExt.Probability.Statistics.LinearModel
