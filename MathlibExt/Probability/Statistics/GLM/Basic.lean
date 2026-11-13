/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GLM.IRLS
public import MathlibExt.Analysis.Calculus.DotProductGradient
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Order.Filter.Extr
import Mathlib.Analysis.Convex.Deriv

/-!
# Canonical exponential-family generalized linear models

A *canonical (natural) exponential family* with dispersion `φ > 0` has per-observation density
`exp ((y θ - b θ) / φ + c (y, φ))` with respect to a base measure carried by a response support
`S ⊆ ℝ`, for natural parameters `θ` in an open convex domain `Θ ⊆ ℝ`. Its *cumulant* `b` has
derivative `b' = μ` (the mean function) and second derivative `b'' = V` (the variance function)
on `Θ`, and `V ≥ 0` on `Θ`. `CanonicalExpFamily` records exactly these data: `natDomain = Θ`,
`support = S`, `cumulant = b`, `mean = μ`, `variance = V`. The family is given by its cumulant
calculus, not by a measure; the base-measure term `c` does not depend on the coefficients and is
omitted.

A generalized linear model with *canonical link* sets `θᵢ = ηᵢ`, where observations are indexed by
a finite type `ι`, coefficients by a finite type `κ`, `X : Matrix ι κ ℝ` is the design and
`o : ι → ℝ` a fixed offset (never fitted): `η(β) = X β + o` (`glmPredictor`). The dispersion `φ`
is fixed. The coefficients are restricted to `glmDomain`, the `β` with every `ηᵢ(β) ∈ Θ`; it is
open and convex (`isOpen_glmDomain`, `convex_glmDomain`).

The log likelihood, up to the `β`-free term `∑ᵢ c (yᵢ, φ)`, is
`ℓ(β) = ∑ᵢ (yᵢ ηᵢ(β) - b (ηᵢ(β))) / φ` (`glmLogLik`). It is a log density only for responses
`yᵢ ∈ S`; every statement below holds for all real `y`.

## Main results

* `hasFDerivAt_glmLogLik`, `hasGradientAt_glmLogLik`: on `glmDomain` the derivative of `ℓ` at
  `β` is `v ↦ ⟪v, Xᵀ (y - μ(η(β))) / φ⟫`, i.e. the score is `glmScore = φ⁻¹ • Xᵀ (y - μ)`.
* `hasFDerivAt_glmScore`: on `glmDomain` the derivative of the score is the Hessian
  `glmHessian = -(φ⁻¹ • Xᵀ W X)` with weights `Wᵢ = V (ηᵢ(β))` (`glmWeights`); it does not depend
  on `y` (observed and Fisher information coincide for canonical links).
* `dotProduct_glmHessian_mulVec`: `uᵀ H u = -φ⁻¹ ∑ᵢ Wᵢ ((X u)ᵢ)²`; `glmHessian_negDef`: with
  full column rank (`X.mulVec` injective) and strictly positive variance on `Θ`, `H` is negative
  definite at every `β ∈ glmDomain`.
* `concaveOn_glmLogLik`: `ℓ` is concave on `glmDomain`.
* `glmLogLik_maximizer_unique`: with full column rank and strictly positive variance on `Θ`, `ℓ`
  has at most one maximizer in `glmDomain`. Existence is not claimed and can fail (for instance
  complete separation in logistic regression).
* `isCanonicalScoreHessian_glm`: with zero offset and unit dispersion, `glmScore` and
  `glmHessian` satisfy the hypotheses `IRLS.IsCanonicalScoreHessian` of the Newton–IRLS
  equivalence.

## References

* J. A. Nelder and R. W. M. Wedderburn, *Generalized linear models*, J. Roy. Statist. Soc.
  Ser. A 135 (1972), 370–384.
* P. McCullagh and J. A. Nelder, *Generalized Linear Models*, 2nd ed., Chapman & Hall, 1989,
  §2.2 and §2.5.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.GLM

open Finset Matrix

/-- A canonical one-parameter exponential family with natural-parameter domain `natDomain` (open,
convex), response support `support`, cumulant `b = cumulant`, mean function `μ = mean = b'` and
variance function `V = variance = b''` on the domain, with `V ≥ 0` there. -/
structure CanonicalExpFamily where
  /-- The natural-parameter domain `Θ`. -/
  natDomain : Set ℝ
  isOpen_natDomain : IsOpen natDomain
  convex_natDomain : Convex ℝ natDomain
  /-- The support of the response distribution; the log likelihood is a log density only for
  responses in it. -/
  support : Set ℝ
  /-- The cumulant (log-partition) function `b`. -/
  cumulant : ℝ → ℝ
  /-- The mean function `μ = b'`. -/
  mean : ℝ → ℝ
  /-- The variance function `V = b''`. -/
  variance : ℝ → ℝ
  hasDerivAt_cumulant : ∀ θ ∈ natDomain, HasDerivAt cumulant (mean θ) θ
  hasDerivAt_mean : ∀ θ ∈ natDomain, HasDerivAt mean (variance θ) θ
  variance_nonneg : ∀ θ ∈ natDomain, 0 ≤ variance θ

variable {ι κ : Type*} [Fintype κ]

/-- The linear predictor `η(β) = X β + o` with design `X` and fixed offset `o`. -/
def glmPredictor (X : Matrix ι κ ℝ) (o : ι → ℝ) (β : κ → ℝ) : ι → ℝ :=
  X *ᵥ β + o

theorem glmPredictor_apply (X : Matrix ι κ ℝ) (o : ι → ℝ) (β : κ → ℝ) (i : ι) :
    glmPredictor X o β i = (X *ᵥ β) i + o i := rfl

private lemma glmPredictor_combo (X : Matrix ι κ ℝ) (o : ι → ℝ) (β γ : κ → ℝ) {a b : ℝ}
    (hab : a + b = 1) (i : ι) :
    glmPredictor X o (a • β + b • γ) i = a * glmPredictor X o β i + b * glmPredictor X o γ i := by
  simp only [glmPredictor_apply, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  linear_combination (o i) * hab.symm

private lemma hasFDerivAt_glmPredictor (X : Matrix ι κ ℝ) (o : ι → ℝ) (β : κ → ℝ) (i : ι) :
    HasFDerivAt (fun β => glmPredictor X o β i) (Real.dotL (X i)) β := by
  have e : (fun β => glmPredictor X o β i) = fun β => β ⬝ᵥ X i + o i := by
    funext β
    simp [glmPredictor_apply, Matrix.mulVec, dotProduct_comm]
  rw [e]
  exact (Real.hasFDerivAt_dotProduct (X i) β).add_const (o i)

namespace CanonicalExpFamily

variable (F : CanonicalExpFamily)

/-! ### The cumulant is convex -/

/-- The cumulant is convex on the natural-parameter domain. -/
theorem convexOn_cumulant : ConvexOn ℝ F.natDomain F.cumulant := by
  have hint : interior F.natDomain = F.natDomain := F.isOpen_natDomain.interior_eq
  have hmono : MonotoneOn F.mean F.natDomain :=
    monotoneOn_of_deriv_nonneg F.convex_natDomain
      (fun θ h => (F.hasDerivAt_mean θ h).continuousAt.continuousWithinAt)
      (by
        rw [hint]
        exact fun θ h => (F.hasDerivAt_mean θ h).differentiableAt.differentiableWithinAt)
      (by
        rw [hint]
        intro θ h
        rw [(F.hasDerivAt_mean θ h).deriv]
        exact F.variance_nonneg θ h)
  refine MonotoneOn.convexOn_of_deriv F.convex_natDomain
    (fun θ h => (F.hasDerivAt_cumulant θ h).continuousAt.continuousWithinAt)
    (by
      rw [hint]
      exact fun θ h => (F.hasDerivAt_cumulant θ h).differentiableAt.differentiableWithinAt) ?_
  rw [hint]
  intro a ha b hb hab
  rw [(F.hasDerivAt_cumulant a ha).deriv, (F.hasDerivAt_cumulant b hb).deriv]
  exact hmono ha hb hab

/-- With strictly positive variance on the domain, the cumulant is strictly convex there. -/
theorem strictConvexOn_cumulant (hvar : ∀ θ ∈ F.natDomain, 0 < F.variance θ) :
    StrictConvexOn ℝ F.natDomain F.cumulant := by
  have hint : interior F.natDomain = F.natDomain := F.isOpen_natDomain.interior_eq
  have hmono : StrictMonoOn F.mean F.natDomain :=
    strictMonoOn_of_deriv_pos F.convex_natDomain
      (fun θ h => (F.hasDerivAt_mean θ h).continuousAt.continuousWithinAt)
      (by
        rw [hint]
        intro θ h
        rw [(F.hasDerivAt_mean θ h).deriv]
        exact hvar θ h)
  refine StrictMonoOn.strictConvexOn_of_deriv F.convex_natDomain
    (fun θ h => (F.hasDerivAt_cumulant θ h).continuousAt.continuousWithinAt) ?_
  rw [hint]
  intro a ha b hb hab
  rw [(F.hasDerivAt_cumulant a ha).deriv, (F.hasDerivAt_cumulant b hb).deriv]
  exact hmono ha hb hab

/-! ### Definitions -/

/-- The coefficient domain: the `β` whose linear predictor lies in the natural-parameter domain
in every coordinate. -/
def glmDomain (X : Matrix ι κ ℝ) (o : ι → ℝ) : Set (κ → ℝ) :=
  {β | ∀ i, glmPredictor X o β i ∈ F.natDomain}

/-- The canonical-link log likelihood with fixed dispersion `φ`, up to the `β`-free base-measure
term: `ℓ(β) = ∑ᵢ (yᵢ ηᵢ(β) - b (ηᵢ(β))) / φ`. -/
noncomputable def glmLogLik [Fintype ι] (φ : ℝ) (X : Matrix ι κ ℝ) (o y : ι → ℝ)
    (β : κ → ℝ) : ℝ :=
  ∑ i, (y i * glmPredictor X o β i - F.cumulant (glmPredictor X o β i)) / φ

/-- The score `Xᵀ (y - μ(η(β))) / φ`. -/
noncomputable def glmScore [Fintype ι] (φ : ℝ) (X : Matrix ι κ ℝ) (o y : ι → ℝ)
    (β : κ → ℝ) : κ → ℝ :=
  φ⁻¹ • (Xᵀ *ᵥ (y - fun i => F.mean (glmPredictor X o β i)))

/-- The working weights `Wᵢ = V (ηᵢ(β))`. -/
def glmWeights (X : Matrix ι κ ℝ) (o : ι → ℝ) (β : κ → ℝ) : ι → ℝ :=
  fun i => F.variance (glmPredictor X o β i)

/-- The Hessian `-Xᵀ W X / φ` of the log likelihood. -/
noncomputable def glmHessian [Fintype ι] [DecidableEq ι] [DecidableEq κ] (φ : ℝ)
    (X : Matrix ι κ ℝ) (o : ι → ℝ) (β : κ → ℝ) : Matrix κ κ ℝ :=
  -(φ⁻¹ • IRLS.weightedGram X (F.glmWeights X o β))

/-! ### The coefficient domain -/

/-- The coefficient domain is convex. -/
theorem convex_glmDomain (X : Matrix ι κ ℝ) (o : ι → ℝ) : Convex ℝ (F.glmDomain X o) := by
  intro β hβ γ hγ a b ha hb hab i
  rw [glmPredictor_combo X o β γ hab i]
  simpa [smul_eq_mul] using F.convex_natDomain (hβ i) (hγ i) ha hb hab

/-- The coefficient domain is open. -/
theorem isOpen_glmDomain [Finite ι] (X : Matrix ι κ ℝ) (o : ι → ℝ) :
    IsOpen (F.glmDomain X o) := by
  have e : F.glmDomain X o = ⋂ i, (fun β => glmPredictor X o β i) ⁻¹' F.natDomain := by
    ext β
    simp [glmDomain]
  rw [e]
  exact isOpen_iInter_of_finite fun i =>
    F.isOpen_natDomain.preimage
      (continuous_iff_continuousAt.2 fun β => (hasFDerivAt_glmPredictor X o β i).continuousAt)

variable [Fintype ι]

/-! ### Score and Hessian -/

private lemma hasDerivAt_term (y φ x : ℝ) (hx : x ∈ F.natDomain) :
    HasDerivAt (fun x => (y * x - F.cumulant x) / φ) ((y - F.mean x) / φ) x := by
  simpa using (((hasDerivAt_id x).const_mul y).sub (F.hasDerivAt_cumulant x hx)).div_const φ

/-- **The score.** On the coefficient domain, the derivative of the log likelihood at `β` is
`v ↦ ⟪v, Xᵀ (y - μ(η(β))) / φ⟫`. -/
theorem hasFDerivAt_glmLogLik (φ : ℝ) (X : Matrix ι κ ℝ) (o y : ι → ℝ) {β : κ → ℝ}
    (hβ : β ∈ F.glmDomain X o) :
    HasFDerivAt (F.glmLogLik φ X o y) (Real.dotL (F.glmScore φ X o y β)) β := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (F.hasDerivAt_term (y i) φ _ (hβ i)).comp_hasFDerivAt β (hasFDerivAt_glmPredictor X o β i)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul, Real.dotL_apply, glmScore]
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul,
    Pi.sub_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The score is the gradient of the log likelihood on `EuclideanSpace ℝ κ`. -/
theorem hasGradientAt_glmLogLik (φ : ℝ) (X : Matrix ι κ ℝ) (o y : ι → ℝ) {β : κ → ℝ}
    (hβ : β ∈ F.glmDomain X o) :
    HasGradientAt (fun b : EuclideanSpace ℝ κ => F.glmLogLik φ X o y b.ofLp)
      (WithLp.toLp 2 (F.glmScore φ X o y β)) (WithLp.toLp 2 β) :=
  Real.hasGradientAt_ofLp (F.hasFDerivAt_glmLogLik φ X o y hβ)

variable [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq κ] in
private lemma transpose_mulVec_weights (X : Matrix ι κ ℝ) (w : ι → ℝ) (v : κ → ℝ) :
    Xᵀ *ᵥ (w * (X *ᵥ v)) = IRLS.weightedGram X w *ᵥ v := by
  have hd : diagonal w *ᵥ (X *ᵥ v) = w * (X *ᵥ v) := funext fun i => by simp [mulVec_diagonal]
  rw [IRLS.weightedGram, ← mulVec_mulVec, ← mulVec_mulVec, hd]

/-- **The Hessian.** On the coefficient domain, the derivative of the score at `β` is
`-Xᵀ W(β) X / φ`, which does not depend on `y`. -/
theorem hasFDerivAt_glmScore (φ : ℝ) (X : Matrix ι κ ℝ) (o y : ι → ℝ) {β : κ → ℝ}
    (hβ : β ∈ F.glmDomain X o) :
    HasFDerivAt (F.glmScore φ X o y)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (F.glmHessian φ X o β))) β := by
  set T : (ι → ℝ) →L[ℝ] (κ → ℝ) := LinearMap.toContinuousLinearMap (Matrix.toLin' Xᵀ)
  have hg : HasFDerivAt (fun β' i => F.mean (glmPredictor X o β' i))
      (ContinuousLinearMap.pi fun i =>
        F.variance (glmPredictor X o β i) • Real.dotL (X i)) β :=
    hasFDerivAt_pi.mpr fun i =>
      (F.hasDerivAt_mean _ (hβ i)).comp_hasFDerivAt β (hasFDerivAt_glmPredictor X o β i)
  have hT := (T.hasFDerivAt.comp β (hg.const_sub y)).const_smul φ⁻¹
  refine hT.congr_fderiv (ContinuousLinearMap.ext fun v => funext fun j => ?_)
  have e : (ContinuousLinearMap.pi fun i =>
      F.variance (glmPredictor X o β i) • Real.dotL (X i)) v = F.glmWeights X o β * (X *ᵥ v) := by
    funext i
    simp [glmWeights, Matrix.mulVec, dotProduct_comm, Real.dotL_apply]
  simp only [T, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply,
    _root_.neg_apply, smul_eq_mul, mulVec_neg, Pi.neg_apply, mul_neg]
  rw [e, glmHessian, neg_mulVec, smul_mulVec, ← transpose_mulVec_weights]
  rfl

/-- The Hessian quadratic form: `uᵀ H(β) u = -φ⁻¹ ∑ᵢ Wᵢ ((X u)ᵢ)²`. -/
theorem dotProduct_glmHessian_mulVec (φ : ℝ) (X : Matrix ι κ ℝ) (o : ι → ℝ) (β u : κ → ℝ) :
    u ⬝ᵥ (F.glmHessian φ X o β *ᵥ u) =
      -(φ⁻¹ * ∑ i, F.glmWeights X o β i * (X *ᵥ u) i ^ 2) := by
  rw [glmHessian, neg_mulVec, smul_mulVec, ← transpose_mulVec_weights, dotProduct_neg,
    dotProduct_smul, dotProduct_mulVec, vecMul_transpose, smul_eq_mul]
  congr 2
  simp only [dotProduct, Pi.mul_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Negative definite Hessian.** With full column rank (`X.mulVec` injective), strictly positive
variance on the natural-parameter domain and `φ > 0`, the Hessian is negative definite at every
`β` in the coefficient domain. -/
theorem glmHessian_negDef {φ : ℝ} (hφ : 0 < φ) {X : Matrix ι κ ℝ} (hX : Function.Injective X.mulVec)
    (hvar : ∀ θ ∈ F.natDomain, 0 < F.variance θ) (o : ι → ℝ) {β : κ → ℝ}
    (hβ : β ∈ F.glmDomain X o) {u : κ → ℝ} (hu : u ≠ 0) :
    u ⬝ᵥ (F.glmHessian φ X o β *ᵥ u) < 0 := by
  rw [dotProduct_glmHessian_mulVec, neg_neg_iff_pos]
  refine mul_pos (inv_pos.2 hφ) ?_
  obtain ⟨j, hj⟩ : ∃ j, (X *ᵥ u) j ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (hX (by rw [mulVec_zero]; exact funext h))
  refine Finset.sum_pos' (fun i _ => mul_nonneg (hvar _ (hβ i)).le (sq_nonneg _))
    ⟨j, Finset.mem_univ j, mul_pos (hvar _ (hβ j)) (by positivity)⟩

omit [DecidableEq ι] [DecidableEq κ]

/-! ### Concavity and at most one maximizer -/

private lemma concaveOn_term {φ : ℝ} (hφ : 0 < φ) (y : ℝ) :
    ConcaveOn ℝ F.natDomain (fun x => (y * x - F.cumulant x) / φ) := by
  refine ⟨F.convex_natDomain, fun x hx z hz a c ha hc hac => ?_⟩
  have h := F.convexOn_cumulant.2 hx hz ha hc hac
  simp only [smul_eq_mul] at h ⊢
  have e : (y * (a * x + c * z) - F.cumulant (a * x + c * z)) / φ -
      (a * ((y * x - F.cumulant x) / φ) + c * ((y * z - F.cumulant z) / φ)) =
      (a * F.cumulant x + c * F.cumulant z - F.cumulant (a * x + c * z)) / φ := by
    field_simp
    ring
  linarith [div_nonneg (sub_nonneg.2 h) hφ.le]

private lemma strictConcaveOn_term {φ : ℝ} (hφ : 0 < φ)
    (hvar : ∀ θ ∈ F.natDomain, 0 < F.variance θ) (y : ℝ) :
    StrictConcaveOn ℝ F.natDomain (fun x => (y * x - F.cumulant x) / φ) := by
  refine ⟨F.convex_natDomain, fun x hx z hz hxz a c ha hc hac => ?_⟩
  have h := (F.strictConvexOn_cumulant hvar).2 hx hz hxz ha hc hac
  simp only [smul_eq_mul] at h ⊢
  have e : (y * (a * x + c * z) - F.cumulant (a * x + c * z)) / φ -
      (a * ((y * x - F.cumulant x) / φ) + c * ((y * z - F.cumulant z) / φ)) =
      (a * F.cumulant x + c * F.cumulant z - F.cumulant (a * x + c * z)) / φ := by
    field_simp
    ring
  linarith [div_pos (sub_pos.2 h) hφ]

/-- **Concavity.** For `φ > 0` the log likelihood is concave on the coefficient domain. -/
theorem concaveOn_glmLogLik {φ : ℝ} (hφ : 0 < φ) (X : Matrix ι κ ℝ) (o y : ι → ℝ) :
    ConcaveOn ℝ (F.glmDomain X o) (F.glmLogLik φ X o y) := by
  refine ⟨F.convex_glmDomain X o, fun β hβ γ hγ a b ha hb hab => ?_⟩
  simp only [glmLogLik, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [glmPredictor_combo X o β γ hab]
  simpa [smul_eq_mul] using (F.concaveOn_term hφ (y i)).2 (hβ i) (hγ i) ha hb hab

/-- **At most one maximizer.** With full column rank (`X.mulVec` injective), strictly positive
variance (hence strictly positive weights) on the natural-parameter domain and `φ > 0`, the log
likelihood has at most one maximizer in the coefficient domain. Existence is not claimed. -/
theorem glmLogLik_maximizer_unique {φ : ℝ} (hφ : 0 < φ) {X : Matrix ι κ ℝ}
    (hX : Function.Injective X.mulVec) (hvar : ∀ θ ∈ F.natDomain, 0 < F.variance θ)
    (o y : ι → ℝ) {β₁ β₂ : κ → ℝ} (hβ₁ : β₁ ∈ F.glmDomain X o) (hβ₂ : β₂ ∈ F.glmDomain X o)
    (h₁ : IsMaxOn (F.glmLogLik φ X o y) (F.glmDomain X o) β₁)
    (h₂ : IsMaxOn (F.glmLogLik φ X o y) (F.glmDomain X o) β₂) : β₁ = β₂ := by
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, glmPredictor X o β₁ j ≠ glmPredictor X o β₂ j := by
    by_contra hall
    push Not at hall
    exact hne (hX (funext fun i => by simpa [glmPredictor_apply] using hall i))
  have hab : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  have hm : (1 / 2 : ℝ) • β₁ + (1 / 2 : ℝ) • β₂ ∈ F.glmDomain X o :=
    F.convex_glmDomain X o hβ₁ hβ₂ (by norm_num) (by norm_num) hab
  have hlt : (1 / 2 : ℝ) * F.glmLogLik φ X o y β₁ + 1 / 2 * F.glmLogLik φ X o y β₂ <
      F.glmLogLik φ X o y ((1 / 2 : ℝ) • β₁ + (1 / 2 : ℝ) • β₂) := by
    simp only [glmLogLik, Finset.mul_sum, ← Finset.sum_add_distrib,
      glmPredictor_combo X o β₁ β₂ hab]
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
    · simpa [smul_eq_mul] using
        (F.concaveOn_term hφ (y i)).2 (hβ₁ i) (hβ₂ i) (by norm_num) (by norm_num) hab
    · simpa [smul_eq_mul] using
        (F.strictConcaveOn_term hφ hvar (y j)).2 (hβ₁ j) (hβ₂ j) hj (by norm_num) (by norm_num)
          hab
  have e₁ := h₁ hβ₂
  have e₂ := h₂ hβ₁
  have em := h₁ hm
  simp only [Set.mem_ofPred_eq] at e₁ e₂ em
  linarith

/-- The set of maximizers in the coefficient domain is a subsingleton under the hypotheses of
`glmLogLik_maximizer_unique`. -/
theorem subsingleton_glmLogLik_maximizers {φ : ℝ} (hφ : 0 < φ) {X : Matrix ι κ ℝ}
    (hX : Function.Injective X.mulVec) (hvar : ∀ θ ∈ F.natDomain, 0 < F.variance θ)
    (o y : ι → ℝ) :
    {β | β ∈ F.glmDomain X o ∧ IsMaxOn (F.glmLogLik φ X o y) (F.glmDomain X o) β}.Subsingleton :=
  fun _ h₁ _ h₂ => F.glmLogLik_maximizer_unique hφ hX hvar o y h₁.1 h₂.1 h₁.2 h₂.2

/-! ### Link to Newton–Raphson as IRLS -/

/-- With zero offset and unit dispersion, the score and Hessian satisfy the canonical-link
hypotheses `IRLS.IsCanonicalScoreHessian`, so the Newton–IRLS results of `GLM.IRLS` apply. -/
theorem isCanonicalScoreHessian_glm [DecidableEq ι] [DecidableEq κ] (X : Matrix ι κ ℝ)
    (y : ι → ℝ) :
    IRLS.IsCanonicalScoreHessian X y F.mean F.variance (F.glmScore 1 X 0 y)
      (F.glmHessian 1 X 0) where
  score_eq β := by simp [glmScore, glmPredictor]
  hess_eq β := by
    simp only [glmHessian, inv_one, one_smul, neg_inj]
    congr 1
    funext i
    simp [glmWeights, glmPredictor, IRLS.irlsWeights]

end CanonicalExpFamily

end MathlibExt.Probability.Statistics.GLM
