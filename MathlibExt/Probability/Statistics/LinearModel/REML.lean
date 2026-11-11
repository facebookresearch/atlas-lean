/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.GaussianDensity
public import MathlibExt.Probability.Distributions.GaussianConditioning

/-!
# Restricted (residual) maximum likelihood: error contrasts and basis invariance

REML (Patterson and Thompson 1971) estimates the covariance parameters `θ` of a Gaussian linear
model `y ~ N(X β, V θ)` from error contrasts. Here `X : Matrix m k ℝ` is a fixed design and
`V : Θ → Matrix m m ℝ` is a family of positive definite covariances. An
**error contrast** (`IsErrorContrast`) is a matrix `A : Matrix r m ℝ` with `A X = 0`, full row
rank (`A Aᵀ` invertible) and `card r + card k = card m`. The contrast vector `z = A y` then
has law `N(0, A V Aᵀ)` whatever `β` is (`hasLaw_errorContrast`), with density
`multivariateGaussianPDFReal 0 (A V Aᵀ)` with respect to Lebesgue measure
(`hasLaw_errorContrast_withDensity`).

The **restricted log-likelihood** `remlLogLik A V y` is the logarithm of that density at
`A y`. It is an actual log density, not a criterion up to an additive constant. For positive
definite `A V Aᵀ`, `remlLogLik_eq` expands it to

  `-(r/2) log (2π) - (1/2) log det (A V Aᵀ) - (1/2) (A y)ᵀ (A V Aᵀ)⁻¹ (A y)`.

The criterion depends on the choice of `A`, but only through an additive constant. If
`B = Q A` with `Q` invertible, then `remlLogLik B V y = remlLogLik A V y - log |det Q|`
(`remlLogLik_mul_left`). So the argmax sets over `θ` (`isMaxOn_remlLogLik_mul_left_iff`) and
the scores (`fderiv_remlLogLik_mul_left`) agree. Any two error contrasts of the same design are
related this way (`exists_eq_mul_of_isErrorContrast`), so the REML estimator does not depend on
which error contrast is used.

Singular covariances are excluded by hypothesis, not totalized. Every result about the criterion
assumes `A V Aᵀ` positive definite, directly or through `V θ` positive definite and `A` of full
row rank. On a singular `A V Aᵀ`, `remlLogLik` is the junk value
`log 0 = 0`, and the identity `remlLogLik_mul_left` fails there.

## Main results

* `IsErrorContrast`: `A X = 0`, `A Aᵀ` invertible, `card r = card m - card k`.
* `posDef_mul_mul_transpose`: `A V Aᵀ` is positive definite for positive definite `V`.
* `hasLaw_errorContrast`, `hasLaw_errorContrast_withDensity`: `A y ~ N(0, A V Aᵀ)`, with
  density.
* `remlLogLik`, `remlLogLik_eq`: the restricted log-likelihood and its closed form.
* `remlLogLik_mul_left`: `ℓ_{QA} = ℓ_A - log |det Q|`.
* `isMaxOn_remlLogLik_mul_left_iff`, `fderiv_remlLogLik_mul_left`: argmax sets and scores do
  not depend on the contrast basis.
* `exists_eq_mul_of_isErrorContrast`: two error contrasts of a full-rank design differ by an
  invertible `Q`.

## References

* H. D. Patterson, R. Thompson, *Recovery of inter-block information when block sizes are
  unequal*, Biometrika 58 (1971), 545–554.
* D. A. Harville, *Bayesian inference for variance components using only error contrasts*,
  Biometrika 61 (1974), 383–385.
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory MetaMathlibExt WithLp

namespace MathlibExt.Probability.Statistics.LinearModel

variable {m k r : Type*} [Fintype m] [Fintype k] [Fintype r] [DecidableEq r]

/-- `A : Matrix r m ℝ` is an **error contrast** for the design `X : Matrix m k ℝ`: it
annihilates the mean space (`A X = 0`), has full row rank (`A Aᵀ` invertible), and has
`card m - card k` rows. -/
structure IsErrorContrast (X : Matrix m k ℝ) (A : Matrix r m ℝ) : Prop where
  mul_eq_zero : A * X = 0
  isUnit_mul_transpose : IsUnit (A * Aᵀ)
  card_add_card : Fintype.card r + Fintype.card k = Fintype.card m

/-- The **restricted (REML) log-likelihood** of the error contrast `A` at covariance `V` and data
`y`: the logarithm of the `N(0, A V Aᵀ)` density at `A y`. See `remlLogLik_eq` for the closed
form when `A V Aᵀ` is positive definite. -/
noncomputable def remlLogLik (A : Matrix r m ℝ) (V : Matrix m m ℝ) (y : m → ℝ) : ℝ :=
  Real.log (multivariateGaussianPDFReal 0 (A * V * Aᵀ) (toLp 2 (A *ᵥ y)))

/-- Full row rank: `A Aᵀ` invertible makes `x ↦ x A` injective. -/
theorem vecMul_injective_of_isUnit {A : Matrix r m ℝ} (hA : IsUnit (A * Aᵀ)) :
    Function.Injective A.vecMul := by
  have hdet : IsUnit (A * Aᵀ).det := (isUnit_iff_isUnit_det _).mp hA
  intro x y (hxy : x ᵥ* A = y ᵥ* A)
  have h : (x - y) ᵥ* (A * Aᵀ) = 0 := by
    rw [← vecMul_vecMul, sub_vecMul, hxy, sub_self, zero_vecMul]
  exact sub_eq_zero.mp (eq_zero_of_vecMul_eq_zero (det_ne_zero_of_left_inverse
    (nonsing_inv_mul _ hdet)) h)

/-- `A V Aᵀ` is positive definite when `V` is and `A` has full row rank. -/
theorem posDef_mul_mul_transpose {A : Matrix r m ℝ} {V : Matrix m m ℝ} (hV : V.PosDef)
    (hA : IsUnit (A * Aᵀ)) : (A * V * Aᵀ).PosDef := by
  simpa [conjTranspose_eq_transpose_of_trivial] using
    hV.mul_mul_conjTranspose_same (vecMul_injective_of_isUnit hA)

/-- **Closed form of the restricted log-likelihood**: for positive definite `S = A V Aᵀ`,
`ℓ_A = -(r/2) log (2π) - (1/2) log det S - (1/2) (A y)ᵀ S⁻¹ (A y)`. -/
theorem remlLogLik_eq {A : Matrix r m ℝ} {V : Matrix m m ℝ} (hS : (A * V * Aᵀ).PosDef)
    (y : m → ℝ) :
    remlLogLik A V y = -(Fintype.card r / 2 * Real.log (2 * Real.pi)) -
      Real.log (A * V * Aᵀ).det / 2 - (A *ᵥ y) ⬝ᵥ (A * V * Aᵀ)⁻¹ *ᵥ (A *ᵥ y) / 2 := by
  have hdet := hS.det_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [remlLogLik, multivariateGaussianPDFReal, sub_zero, Real.log_mul (by positivity)
    (Real.exp_pos _).ne', Real.log_mul (by positivity) (by positivity), Real.log_exp,
    Real.log_inv, Real.log_inv, Real.log_pow, Real.log_sqrt h2π.le, Real.log_sqrt hdet.le]
  ring

/-! ### The law of an error contrast -/

section Law

variable [DecidableEq m] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Law of an error contrast**: if `y ~ N(X β, V)` and `A X = 0`, then `A y ~ N(0, A V Aᵀ)`,
whatever `β` is. This is a statement about the law, not only the first two moments. -/
theorem hasLaw_errorContrast {X : Matrix m k ℝ} {A : Matrix r m ℝ} (hAX : A * X = 0)
    {V : Matrix m m ℝ} (hV : V.PosSemidef) (β : k → ℝ) {y : Ω → EuclideanSpace ℝ m}
    (hy : HasLaw y (multivariateGaussian (toLp 2 (X *ᵥ β)) V) μ) :
    HasLaw (fun ω => toEuclideanLin A (y ω)) (multivariateGaussian 0 (A * V * Aᵀ)) μ := by
  refine HasLaw.fun_comp (Y := toEuclideanLin A)
    ⟨(continuous_toEuclideanLin A).aemeasurable, ?_⟩ hy
  rw [map_toEuclideanLin_multivariateGaussian A _ hV]
  congr 1
  change toLp 2 (A *ᵥ (X *ᵥ β)) = 0
  rw [mulVec_mulVec, hAX, zero_mulVec, toLp_zero]

omit [DecidableEq r] in
/-- **Mean and covariance of an error contrast**: if `y ~ N(X β, V)` and `A X = 0`, then
`𝔼[A y] = 0` and `Cov((A y) i, (A y) j) = (A V Aᵀ) i j`. -/
theorem integral_covariance_errorContrast {X : Matrix m k ℝ} {A : Matrix r m ℝ}
    (hAX : A * X = 0) {V : Matrix m m ℝ} (hV : V.PosSemidef) (β : k → ℝ)
    {y : Ω → EuclideanSpace ℝ m}
    (hy : HasLaw y (multivariateGaussian (toLp 2 (X *ᵥ β)) V) μ) :
    ∫ ω, toEuclideanLin A (y ω) ∂μ = 0 ∧
      ∀ i j, cov[fun ω => toEuclideanLin A (y ω) i, fun ω => toEuclideanLin A (y ω) j; μ] =
        (A * V * Aᵀ) i j := by
  classical
  have hz := hasLaw_errorContrast hAX hV β hy
  have hS : (A * V * Aᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hV.mul_mul_conjTranspose_same A
  refine ⟨by rw [hz.integral_eq, integral_id_multivariateGaussian], fun i j => ?_⟩
  rw [hz.covariance_fun_comp (f := fun x => x i) (g := fun x => x j) (by fun_prop)
    (by fun_prop), covariance_eval_multivariateGaussian hS]

/-- **Density of an error contrast**: if `y ~ N(X β, V)` with `V` positive definite and `A` is
an error contrast, then `A y` has density `multivariateGaussianPDFReal 0 (A V Aᵀ)`. Its
logarithm at `A y` is `remlLogLik A V y` (`remlLogLik_toEuclideanLin`). -/
theorem hasLaw_errorContrast_withDensity {X : Matrix m k ℝ} {A : Matrix r m ℝ}
    (hA : IsErrorContrast X A) {V : Matrix m m ℝ} (hV : V.PosDef) (β : k → ℝ)
    {y : Ω → EuclideanSpace ℝ m}
    (hy : HasLaw y (multivariateGaussian (toLp 2 (X *ᵥ β)) V) μ) :
    HasLaw (fun ω => toEuclideanLin A (y ω))
      (volume.withDensity fun z => ENNReal.ofReal (multivariateGaussianPDFReal 0 (A * V * Aᵀ) z))
      μ := by
  rw [← multivariateGaussian_eq_withDensity 0
    (posDef_mul_mul_transpose hV hA.isUnit_mul_transpose)]
  exact hasLaw_errorContrast hA.mul_eq_zero hV.posSemidef β hy

/-- `remlLogLik A V y` is the log density of `N(0, A V Aᵀ)` at the contrast vector `A y`. -/
theorem remlLogLik_toEuclideanLin (A : Matrix r m ℝ) (V : Matrix m m ℝ)
    (y : EuclideanSpace ℝ m) :
    remlLogLik A V (ofLp y) =
      Real.log (multivariateGaussianPDFReal 0 (A * V * Aᵀ) (toEuclideanLin A y)) :=
  rfl

end Law

/-! ### Invariance under a change of contrast basis -/

omit [DecidableEq r] in
private theorem dotProduct_mulVec_mulVec_left (Q W : Matrix r r ℝ) (u : r → ℝ) :
    (Q *ᵥ u) ⬝ᵥ W *ᵥ (Q *ᵥ u) = u ⬝ᵥ (Qᵀ * W * Q) *ᵥ u := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u Qᵀ, vecMul_transpose]

/-- **Change of contrast basis**: if `B = Q A` with `Q` invertible, the restricted
log-likelihoods differ by the constant `log |det Q|`: `ℓ_{QA} = ℓ_A - log |det Q|`, for every
covariance with `A V Aᵀ` positive definite and every `y`. -/
theorem remlLogLik_mul_left {A : Matrix r m ℝ} {V : Matrix m m ℝ} (hS : (A * V * Aᵀ).PosDef)
    {Q : Matrix r r ℝ} (hQ : IsUnit Q.det) (y : m → ℝ) :
    remlLogLik (Q * A) V y = remlLogLik A V y - Real.log |Q.det| := by
  have hQA : Q * A * V * (Q * A)ᵀ = Q * (A * V * Aᵀ) * Qᵀ := by
    rw [transpose_mul]; simp only [Matrix.mul_assoc]
  have hS' : (Q * A * V * (Q * A)ᵀ).PosDef := by
    rw [hQA]
    simpa [conjTranspose_eq_transpose_of_trivial] using
      hS.mul_mul_conjTranspose_same (vecMul_injective_iff_isUnit.mpr
        ((isUnit_iff_isUnit_det _).mpr hQ))
  have hQ0 : Q.det ≠ 0 := hQ.ne_zero
  have hdet : (Q * A * V * (Q * A)ᵀ).det = |Q.det| ^ 2 * (A * V * Aᵀ).det := by
    rw [hQA, det_mul, det_mul, det_transpose, sq_abs]; ring
  have hquad : ((Q * A) *ᵥ y) ⬝ᵥ (Q * A * V * (Q * A)ᵀ)⁻¹ *ᵥ ((Q * A) *ᵥ y) =
      (A *ᵥ y) ⬝ᵥ (A * V * Aᵀ)⁻¹ *ᵥ (A *ᵥ y) := by
    have hQt : IsUnit Qᵀ.det := by rwa [det_transpose]
    rw [← mulVec_mulVec, dotProduct_mulVec_mulVec_left, hQA, Matrix.mul_inv_rev,
      Matrix.mul_inv_rev]
    congr 2
    rw [show Qᵀ * (Qᵀ⁻¹ * ((A * V * Aᵀ)⁻¹ * Q⁻¹)) * Q =
        (Qᵀ * Qᵀ⁻¹) * (A * V * Aᵀ)⁻¹ * (Q⁻¹ * Q) by simp only [Matrix.mul_assoc],
      mul_nonsing_inv _ hQt, nonsing_inv_mul _ hQ, Matrix.one_mul, Matrix.mul_one]
  rw [remlLogLik_eq hS', remlLogLik_eq hS, hdet, hquad,
    Real.log_mul (by positivity) hS.det_pos.ne', Real.log_pow]
  push_cast
  ring

/-- **Argmax invariance**: under a change of contrast basis `B = Q A`, the restricted
log-likelihoods of `A` and `B` have the same maximizers over every set of parameters. -/
theorem isMaxOn_remlLogLik_mul_left_iff {Θ : Type*} {A : Matrix r m ℝ}
    (hA : IsUnit (A * Aᵀ)) {V : Θ → Matrix m m ℝ} (hV : ∀ θ, (V θ).PosDef)
    {Q : Matrix r r ℝ} (hQ : IsUnit Q.det) (y : m → ℝ) (s : Set Θ) (θ₀ : Θ) :
    IsMaxOn (fun θ => remlLogLik (Q * A) (V θ) y) s θ₀ ↔
      IsMaxOn (fun θ => remlLogLik A (V θ) y) s θ₀ := by
  simp only [isMaxOn_iff, remlLogLik_mul_left (posDef_mul_mul_transpose (hV _) hA) hQ,
    sub_le_sub_iff_right]

/-- **Score invariance**: for a parameter in a normed space, the restricted log-likelihoods of
`A` and `Q A` have the same derivatives, and one is differentiable exactly where the other is. -/
theorem hasFDerivAt_remlLogLik_mul_left_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {A : Matrix r m ℝ} (hA : IsUnit (A * Aᵀ)) {V : E → Matrix m m ℝ}
    (hV : ∀ θ, (V θ).PosDef) {Q : Matrix r r ℝ} (hQ : IsUnit Q.det) (y : m → ℝ)
    (f' : E →L[ℝ] ℝ) (θ : E) :
    HasFDerivAt (fun θ => remlLogLik (Q * A) (V θ) y) f' θ ↔
      HasFDerivAt (fun θ => remlLogLik A (V θ) y) f' θ := by
  simp only [remlLogLik_mul_left (posDef_mul_mul_transpose (hV _) hA) hQ]
  exact hasFDerivAt_sub_const_iff _

/-- **Score invariance**, `fderiv` form. -/
theorem fderiv_remlLogLik_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Matrix r m ℝ} (hA : IsUnit (A * Aᵀ)) {V : E → Matrix m m ℝ} (hV : ∀ θ, (V θ).PosDef)
    {Q : Matrix r r ℝ} (hQ : IsUnit Q.det) (y : m → ℝ) :
    fderiv ℝ (fun θ => remlLogLik (Q * A) (V θ) y) = fderiv ℝ (fun θ => remlLogLik A (V θ) y) := by
  funext θ
  simp only [remlLogLik_mul_left (posDef_mul_mul_transpose (hV _) hA) hQ]
  exact fderiv_sub_const _

/-! ### Any two error contrasts differ by an invertible matrix -/

omit [DecidableEq r] in
private theorem rank_eq_card_of_isUnit_mul_transpose [DecidableEq r] {A : Matrix r m ℝ}
    (hA : IsUnit (A * Aᵀ)) : A.rank = Fintype.card r :=
  le_antisymm (rank_le_card_height A) ((rank_of_isUnit _ hA).symm.le.trans (rank_mul_le_left _ _))

/-- **Error contrasts are unique up to an invertible matrix**: for a design with invertible
`Xᵀ X`, any two error contrasts `A, B : Matrix r m ℝ` satisfy `B = Q A` with `Q` invertible.
Both row spaces equal the left null space of `X`, which has dimension `card m - card k`. -/
theorem exists_eq_mul_of_isErrorContrast [DecidableEq k] {X : Matrix m k ℝ}
    (hX : IsUnit (Xᵀ * X)) {A B : Matrix r m ℝ} (hA : IsErrorContrast X A)
    (hB : IsErrorContrast X B) : ∃ Q : Matrix r r ℝ, IsUnit Q.det ∧ B = Q * A := by
  classical
  set K := LinearMap.ker (Xᵀ.mulVecLin) with hK
  set R := LinearMap.range (Aᵀ.mulVecLin) with hR
  have hRK : R ≤ K := by
    rintro _ ⟨w, rfl⟩
    change Xᵀ *ᵥ (Aᵀ *ᵥ w) = 0
    rw [mulVec_mulVec, ← transpose_mul, hA.mul_eq_zero, transpose_zero, zero_mulVec]
  have hRfin : Module.finrank ℝ R = Fintype.card r := by
    change Aᵀ.rank = _
    rw [rank_transpose, rank_eq_card_of_isUnit_mul_transpose hA.isUnit_mul_transpose]
  have hXrank : Xᵀ.rank = Fintype.card k := by
    rw [rank_transpose]
    exact le_antisymm (rank_le_card_width X)
      ((rank_of_isUnit _ hX).symm.le.trans (rank_mul_le_right _ _))
  have hKfin : Module.finrank ℝ K = Fintype.card r := by
    have h := Xᵀ.mulVecLin.finrank_range_add_finrank_ker
    rw [Module.finrank_fintype_fun_eq_card] at h
    change Xᵀ.rank + Module.finrank ℝ K = _ at h
    have := hA.card_add_card
    omega
  have hRK' : R = K := Submodule.eq_of_le_of_finrank_eq hRK (by rw [hRfin, hKfin])
  have hrow : ∀ i, ∃ w, Aᵀ *ᵥ w = B i := by
    intro i
    have hmem : B i ∈ K := by
      change Xᵀ *ᵥ B i = 0
      funext j
      have := congrFun (congrFun hB.mul_eq_zero i) j
      simpa [mulVec, dotProduct, Matrix.mul_apply, mul_comm] using this
    rw [← hRK'] at hmem
    exact hmem
  choose W hW using hrow
  have hBQ : B = Matrix.of W * A := by
    ext i j
    rw [← hW i]
    simp [mulVec, dotProduct, Matrix.mul_apply, mul_comm]
  refine ⟨Matrix.of W, ?_, hBQ⟩
  have hBB := (isUnit_iff_isUnit_det _).mp hB.isUnit_mul_transpose
  rw [hBQ, transpose_mul, show Matrix.of W * A * (Aᵀ * (Matrix.of W)ᵀ) =
      Matrix.of W * (A * Aᵀ) * (Matrix.of W)ᵀ by simp only [Matrix.mul_assoc],
    det_mul, det_mul] at hBB
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hBB)

end MathlibExt.Probability.Statistics.LinearModel
