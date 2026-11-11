/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.Sampling
public import MathlibExt.Probability.Distributions.CochranIndependence
public import MathlibExt.Probability.Distributions.StudentT

/-!
# Exact `t` inference for a contrast in the Gaussian linear model

Fixed-design linear model `y = X β + ε` with `X : Matrix m k ℝ` of full column rank
(`IsUnit (Xᵀ X)`), `p = card k < n = card m`, and errors `ε` whose standardized form `σ⁻¹ ε`
(`σ > 0`) has i.i.d. standard normal coordinates. Write `B = (Xᵀ X)⁻¹ Xᵀ` (`olsMatrix`),
`M = 1 - X B` (`residualMatrix`), `β̂ = B y` and `d = n - p`.

* `B Mᵀ = 0`, so `β̂` is independent of the residual vector `y - X β̂` and of
  `‖y - X β̂‖² / σ²`.
* For a contrast `a ≠ 0`, `q = aᵀ (Xᵀ X)⁻¹ a > 0`, `aᵀ (β̂ - β) / (σ √q) ~ N(0, 1)`, and
  `T = aᵀ (β̂ - β) / √((‖y - X β̂‖² / d) · q)` has law `studentTMeasure d`.
* Coverage identity: `P(|T| ≤ c) = t_d([-c, c])` for every `c`. Choosing `c` as a `t_d`
  quantile is numerics and is not done here.

## Main results

* `ProbabilityTheory.pi_gaussianReal_map_dotProduct`: `w ⬝ᵥ Z ~ N(0, w ⬝ᵥ w)` for standard
  Gaussian `Z`.
* `olsMatrix_mul_transpose_residualMatrix`: `B Mᵀ = 0`.
* `indepFun_olsEstimator_residual`, `indepFun_olsEstimator_rss_div_sq`.
* `contrastVariance`, `contrastVariance_pos`.
* `hasLaw_contrast_div`: the standardized contrast is standard normal.
* `tStatistic`, `tStatistic_eq_div_sqrt`: the pointwise identity `T = U / √(V / d)`.
* `hasLaw_tStatistic`: `T ~ t_d`.
* `measureReal_abs_tStatistic_le`: the coverage identity.

Not covered: the `F` law of `T²`, since no ratio-of-chi-squares characterization of
`snedecorFMeasure` is available yet.
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- **Gaussian linear form**: for a standard Gaussian vector `Z` in `ℝ^ι` and a fixed `w`, the
linear form `w ⬝ᵥ Z` has law `N(0, w ⬝ᵥ w)`. -/
theorem pi_gaussianReal_map_dotProduct (w : ι → ℝ) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun x => w ⬝ᵥ x) =
      gaussianReal 0 (w ⬝ᵥ w).toNNReal := by
  set L : StrongDual ℝ (EuclideanSpace ℝ ι) := innerSL ℝ (WithLp.toLp 2 w)
  have hfun : (fun x : ι → ℝ => w ⬝ᵥ x) = L ∘ WithLp.toLp 2 := by
    funext x
    simp [L, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rw [hfun, ← Measure.map_map L.continuous.measurable (PiLp.continuous_toLp 2 _).measurable,
    map_pi_eq_stdGaussian, IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm, EuclideanSpace.real_norm_sq_eq]
  congr 2
  simp [dotProduct, sq]

end ProbabilityTheory

namespace MathlibExt.Probability.Statistics.LinearModel

variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
variable {X : Matrix m k ℝ}

/-! ### Independence of the estimator and the residuals -/

/-- `B Mᵀ = 0` for the OLS matrix `B` and the residual-maker matrix `M`. -/
theorem olsMatrix_mul_transpose_residualMatrix (hX : IsUnit (Xᵀ * X)) :
    olsMatrix X * (residualMatrix X)ᵀ = 0 := by
  rw [residualMatrix_transpose, residualMatrix, Matrix.mul_sub, Matrix.mul_one,
    ← Matrix.mul_assoc, olsMatrix_mul_self hX, Matrix.one_mul, sub_self]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- For a standard Gaussian vector `Z`, `B Z` and `M Z` are independent. -/
theorem indepFun_olsMatrix_mulVec_residualMatrix_mulVec (hX : IsUnit (Xᵀ * X))
    {Z : Ω → m → ℝ} (hZ : HasLaw Z (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    IndepFun (fun ω => olsMatrix X *ᵥ Z ω) (fun ω => residualMatrix X *ᵥ Z ω) μ :=
  indepFun_mulVec_mulVec_of_hasLaw hZ (olsMatrix_mul_transpose_residualMatrix hX)

omit [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k] in
private theorem smul_inv_smul_eq {σ : ℝ} (hσ : 0 < σ) (e : m → ℝ) : σ • σ⁻¹ • e = e := by
  rw [smul_smul, mul_inv_cancel₀ hσ.ne', one_smul]

/-- **Independence of `β̂` and the residuals**: in `y = X β + ε` with `σ > 0` and
`σ⁻¹ ε` standard Gaussian, the OLS estimate `β̂` is independent of the residual vector
`y - X β̂`. -/
theorem indepFun_olsEstimator_residual (hX : IsUnit (Xᵀ * X)) (β : k → ℝ) {ε : Ω → m → ℝ}
    {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    IndepFun (fun ω => olsEstimator X (X *ᵥ β + ε ω))
      (fun ω => X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) μ := by
  have h := (indepFun_olsMatrix_mulVec_residualMatrix_mulVec hX hε).comp
    (φ := fun v => β + σ • v) (ψ := fun v => σ • v) (by fun_prop) (by fun_prop)
  convert h using 2 with ω ω
  · simp only [Function.comp_apply, ← mulVec_smul, smul_inv_smul_eq hσ, olsEstimator_add hX]
  · simp only [Function.comp_apply, ← mulVec_smul, smul_inv_smul_eq hσ,
      sub_mulVec_olsEstimator, residualMatrix_mulVec_add hX]

/-- **Independence of `β̂` and the scaled residual sum of squares**: `β̂` is independent of
`‖y - X β̂‖² / σ²`. -/
theorem indepFun_olsEstimator_rss_div_sq (hX : IsUnit (Xᵀ * X)) (β : k → ℝ) {ε : Ω → m → ℝ}
    {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    IndepFun (fun ω => olsEstimator X (X *ᵥ β + ε ω))
      (fun ω => (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) ⬝ᵥ
        (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) / σ ^ 2) μ :=
  (indepFun_olsEstimator_residual hX β hσ hε).comp (φ := id)
    (ψ := fun r : m → ℝ => r ⬝ᵥ r / σ ^ 2) measurable_id (by fun_prop)

/-! ### The contrast `t` statistic -/

/-- The variance factor `aᵀ (Xᵀ X)⁻¹ a` of the contrast `aᵀ β̂`:
`Var(aᵀ β̂) = σ² · contrastVariance X a`. -/
noncomputable def contrastVariance (X : Matrix m k ℝ) (a : k → ℝ) : ℝ :=
  a ⬝ᵥ ((Xᵀ * X)⁻¹ *ᵥ a)

omit [DecidableEq m] in
/-- For a full-rank design and a nonzero contrast, `aᵀ (Xᵀ X)⁻¹ a > 0`: the Gram matrix is
positive definite, hence so is its inverse. -/
theorem contrastVariance_pos (hX : IsUnit (Xᵀ * X)) {a : k → ℝ} (ha : a ≠ 0) :
    0 < contrastVariance X a := by
  have hpsd : (Xᵀ * X).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self X
  have h := (hpsd.posDef_iff_isUnit.mpr hX).inv.dotProduct_mulVec_pos ha
  simpa [contrastVariance] using h

/-- `‖Bᵀ a‖² = aᵀ (Xᵀ X)⁻¹ a`, from `B Bᵀ = (Xᵀ X)⁻¹`. -/
theorem olsMatrix_transpose_mulVec_dotProduct_self (hX : IsUnit (Xᵀ * X)) (a : k → ℝ) :
    ((olsMatrix X)ᵀ *ᵥ a) ⬝ᵥ ((olsMatrix X)ᵀ *ᵥ a) = contrastVariance X a := by
  conv_lhs => arg 1; rw [mulVec_transpose]
  rw [← dotProduct_mulVec, contrastVariance, ← olsMatrix_mul_transpose hX, mulVec_mulVec]

/-- `aᵀ (B e) = (Bᵀ a) ⬝ᵥ e`. -/
theorem dotProduct_olsMatrix_mulVec (X : Matrix m k ℝ) (a : k → ℝ) (e : m → ℝ) :
    a ⬝ᵥ (olsMatrix X *ᵥ e) = ((olsMatrix X)ᵀ *ᵥ a) ⬝ᵥ e := by
  rw [dotProduct_mulVec, mulVec_transpose]

/-- **Standardized contrast**: for a nonzero contrast `a`,
`aᵀ (β̂ - β) / (σ √(aᵀ (Xᵀ X)⁻¹ a)) ~ N(0, 1)`. -/
theorem hasLaw_contrast_div (hX : IsUnit (Xᵀ * X)) (β : k → ℝ) {ε : Ω → m → ℝ} {σ : ℝ}
    (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ)
    {a : k → ℝ} (ha : a ≠ 0) :
    HasLaw (fun ω => a ⬝ᵥ (olsEstimator X (X *ᵥ β + ε ω) - β) /
        (σ * √(contrastVariance X a))) (gaussianReal 0 1) μ := by
  have hq := contrastVariance_pos hX ha
  have hsq : 0 < √(contrastVariance X a) := Real.sqrt_pos.mpr hq
  set w : m → ℝ := (√(contrastVariance X a))⁻¹ • ((olsMatrix X)ᵀ *ᵥ a)
  have hw : w ⬝ᵥ w = 1 := by
    simp only [w, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      olsMatrix_transpose_mulVec_dotProduct_self hX]
    rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hq.le, inv_mul_cancel₀ hq.ne']
  have hfun : (fun ω => a ⬝ᵥ (olsEstimator X (X *ᵥ β + ε ω) - β) /
      (σ * √(contrastVariance X a))) = fun ω => w ⬝ᵥ (σ⁻¹ • ε ω) := by
    funext ω
    rw [olsEstimator_add hX, add_sub_cancel_left, dotProduct_olsMatrix_mulVec]
    simp only [w, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    field_simp
  rw [hfun]
  refine HasLaw.fun_comp (Y := fun x => w ⬝ᵥ x) ⟨by fun_prop, ?_⟩ hε
  rw [pi_gaussianReal_map_dotProduct, hw]
  simp

/-- The `t` statistic `aᵀ (β̂ - β) / √((‖y - X β̂‖² / (n - p)) · aᵀ (Xᵀ X)⁻¹ a)` for testing
the value `aᵀ β` of a contrast from observations `y`. -/
noncomputable def tStatistic (X : Matrix m k ℝ) (a β : k → ℝ) (y : m → ℝ) : ℝ :=
  a ⬝ᵥ (olsEstimator X y - β) /
    √((y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y) /
      (Fintype.card m - Fintype.card k : ℕ) * contrastVariance X a)

omit [DecidableEq m] [DecidableEq k] in
/-- Real-number core of `tStatistic_eq_div_sqrt`: for `σ > 0` and `q ≥ 0`,
`N / √(R / d · q) = (N / (σ √q)) / √(R / σ² / d)`. No sign condition on `R` or `d` is
needed: when `√(R / d) = 0` both sides are `0`. -/
private theorem div_sqrt_eq (N R d q σ : ℝ) (hσ : 0 < σ) (hq : 0 ≤ q) :
    N / √(R / d * q) = N / (σ * √q) / √(R / σ ^ 2 / d) := by
  rw [Real.sqrt_mul' _ hq, div_right_comm R, Real.sqrt_div' _ (sq_nonneg σ),
    Real.sqrt_sq hσ.le, div_div_eq_mul_div, mul_comm σ, ← div_div N (√q) σ,
    div_mul_cancel₀ (N / √q) hσ.ne', div_div, mul_comm (√q)]

/-- **Pointwise form of the `t` statistic**: in `y = X β + e`, `T = U / √(V / d)` with
`U = aᵀ (β̂ - β) / (σ √q)` the standardized contrast, `V = ‖y - X β̂‖² / σ²` and `d = n - p`. -/
theorem tStatistic_eq_div_sqrt (a β : k → ℝ) (e : m → ℝ) {σ : ℝ} (hσ : 0 < σ)
    (hq : 0 ≤ contrastVariance X a) :
    tStatistic X a β (X *ᵥ β + e) =
      a ⬝ᵥ (olsEstimator X (X *ᵥ β + e) - β) / (σ * √(contrastVariance X a)) /
        √((X *ᵥ β + e - X *ᵥ olsEstimator X (X *ᵥ β + e)) ⬝ᵥ
          (X *ᵥ β + e - X *ᵥ olsEstimator X (X *ᵥ β + e)) / σ ^ 2 /
            (Fintype.card m - Fintype.card k : ℕ)) :=
  div_sqrt_eq _ _ _ _ σ hσ hq

/-- **Exact `t` law of a contrast**: in `y = X β + ε` with full-rank `X`, `p < n`, `σ > 0`,
`σ⁻¹ ε` standard Gaussian and a nonzero contrast `a`, the statistic
`aᵀ (β̂ - β) / √((‖y - X β̂‖² / (n - p)) · aᵀ (Xᵀ X)⁻¹ a)` has Student's `t` law with `n - p`
degrees of freedom. -/
theorem hasLaw_tStatistic (hX : IsUnit (Xᵀ * X)) (hkm : Fintype.card k < Fintype.card m)
    (β : k → ℝ) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ)
    {a : k → ℝ} (ha : a ≠ 0) :
    HasLaw (fun ω => tStatistic X a β (X *ᵥ β + ε ω))
      (studentTMeasure (Fintype.card m - Fintype.card k)) μ := by
  have := hε.isProbabilityMeasure
  have hq := contrastVariance_pos hX ha
  have hU := hasLaw_contrast_div hX β hσ hε ha
  have hV := hasLaw_rss_div_sq hX hkm β σ hσ hε
  have hUV := (indepFun_olsEstimator_rss_div_sq hX β hσ hε).comp
    (φ := fun b => a ⬝ᵥ (b - β) / (σ * √(contrastVariance X a))) (ψ := id)
    (by fun_prop) measurable_id
  simp_rw [tStatistic_eq_div_sqrt a β _ hσ hq.le]
  exact ⟨(hU.aemeasurable.div (hV.aemeasurable.div_const _).sqrt),
    map_div_sqrt_chiSquare_eq_studentT (by omega) hU hV hUV⟩

/-- **Coverage identity for the contrast `t` statistic**: for every `c`,
`P(|T| ≤ c) = t_{n-p}([-c, c])`. Taking `c` to be a `t_{n-p}` quantile gives an exact
confidence interval for `aᵀ β`; computing that quantile is outside this file. -/
theorem measureReal_abs_tStatistic_le (hX : IsUnit (Xᵀ * X))
    (hkm : Fintype.card k < Fintype.card m) (β : k → ℝ) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ)
    {a : k → ℝ} (ha : a ≠ 0) (c : ℝ) :
    μ.real {ω | |tStatistic X a β (X *ᵥ β + ε ω)| ≤ c} =
      (studentTMeasure (Fintype.card m - Fintype.card k)).real (Set.Icc (-c) c) := by
  rw [(hasLaw_tStatistic hX hkm β hσ hε ha).measureReal_eq (p := fun t => |t| ≤ c)
    (measurableSet_le (by fun_prop) measurable_const)]
  congr 1
  ext t
  simp [abs_le]

end MathlibExt.Probability.Statistics.LinearModel
