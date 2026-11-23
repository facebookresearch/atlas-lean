/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Fréchet derivative of the norm in a Hilbert space

In an inner product space over `K = ℝ` or `K = ℂ`, the norm is smooth away from
`0`, and its Fréchet derivative at a nonzero point `x` is the norming functional
`y ↦ re ⟪x, y⟫ / ‖x‖`. Mathlib already contains the smoothness statement
(`contDiffAt_norm` in `Mathlib.Analysis.InnerProductSpace.Calculus`), the
derivative of the squared norm (`hasStrictFDerivAt_norm_sq`), and the derivative
of `‖·‖ ^ p` for `p > 1` (`hasFDerivAt_norm_rpow` in
`Mathlib.Analysis.InnerProductSpace.NormPow`), but not the explicit derivative
of the norm itself, nor its consequences for distance functions.

This file supplies that derivative, in strict form, together with its
`fderiv` formula, the fact that the derivative has operator norm `1`, the
chain rule for the norm of a differentiable map, the derivative of the norm
along a curve, tangency of unit-sphere curves, and the gradient of the squared
distance to a point and to a closed subspace (via the orthogonal projection).

This is a companion to the Hilbert-space material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` (inner product
spaces, orthogonal projections, the closest-point property), not one of the
72 v1 targets.

## Main declarations

* `reInnerSL` : the real-linear functional `y ↦ re ⟪x, y⟫`.
* `hasStrictFDerivAt_norm` : the Fréchet derivative of the norm at `x ≠ 0`.
* `fderiv_norm_apply` : `fderiv ℝ (‖·‖) x y = re ⟪x, y⟫ / ‖x‖`.
* `norm_fderiv_norm` : the derivative of the norm at `x ≠ 0` has norm `1`.
* `HasDerivAt.norm` : the derivative of the norm along a curve.
* `re_inner_self_deriv_eq_zero_of_forall_norm_eq_one` : a curve on the unit
  sphere has velocity orthogonal to its position.
* `hasStrictFDerivAt_dist_sq` : the gradient of the squared distance to a point.
* `hasStrictFDerivAt_infDist_sq` : the gradient of the squared distance to a
  closed subspace, `2 • reInnerSL K (x - S.starProjection x)`.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.NormDerivative

variable {K E : Type*} [RCLike K] [NormedAddCommGroup E] [InnerProductSpace K E]
  [NormedSpace ℝ E]

/-- The real-linear functional `y ↦ re ⟪x, y⟫`, the unnormalized gradient of
the norm at `x`. The scalar field `K` is an explicit argument because the
type `E →L[ℝ] ℝ` does not determine it. -/
noncomputable def reInnerSL (K : Type*) [RCLike K] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace K E] [NormedSpace ℝ E] (x : E) : E →L[ℝ] ℝ :=
  (RCLike.reCLM (K := K)).comp ((innerSL K x).restrictScalars ℝ)

@[simp]
theorem reInnerSL_apply (x y : E) : reInnerSL K x y = RCLike.re (inner K x y) := rfl

/-- The derivative of the squared norm is twice the real inner product with `x`. -/
theorem hasStrictFDerivAt_norm_sq (x : E) : HasStrictFDerivAt (fun y : E => ‖y‖ ^ 2)
    (2 • reInnerSL K x) x := by
  have h := (hasStrictFDerivAt_id x).inner K (hasStrictFDerivAt_id x)
  have h2 := (RCLike.reCLM (K := K)).hasStrictFDerivAt.comp x h
  convert h2 using 1
  · ext y
    simp
  · ext y
    simp [fderivInnerCLM_apply, reInnerSL, two_smul, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply]
    rw [← inner_conj_symm, RCLike.conj_re]

/-- The Fréchet derivative of the norm at a nonzero point `x` is the norming
functional `y ↦ re ⟪x, y⟫ / ‖x‖`. -/
theorem hasStrictFDerivAt_norm {x : E} (hx : x ≠ 0) :
    HasStrictFDerivAt (fun y : E => ‖y‖) ((‖x‖⁻¹ : ℝ) • reInnerSL K x) x := by
  have hx2 : (‖x‖ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (norm_pos_iff.mpr hx).ne'
  have h := (hasStrictFDerivAt_norm_sq (K := K) (E := E) x).sqrt hx2
  have hsqrt : ∀ y : E, Real.sqrt (‖y‖ ^ 2) = ‖y‖ := fun y => Real.sqrt_sq (norm_nonneg y)
  simp only [hsqrt] at h
  convert h using 1
  have hxn : (‖x‖ : ℝ) ≠ 0 := (norm_pos_iff.mpr hx).ne'
  ext y
  simp only [smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The non-strict form of `hasStrictFDerivAt_norm`. -/
theorem hasFDerivAt_norm {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) ((‖x‖⁻¹ : ℝ) • reInnerSL K x) x :=
  (hasStrictFDerivAt_norm hx).hasFDerivAt

/-- The `fderiv` of the norm at a nonzero point. -/
theorem fderiv_norm {x : E} (hx : x ≠ 0) :
    fderiv ℝ (fun y : E => ‖y‖) x = (‖x‖⁻¹ : ℝ) • reInnerSL K x :=
  (hasFDerivAt_norm (K := K) (E := E) hx).fderiv

/-- The `fderiv` of the norm at a nonzero point, applied to a vector. -/
theorem fderiv_norm_apply {x y : E} (hx : x ≠ 0) :
    fderiv ℝ (fun z : E => ‖z‖) x y = RCLike.re (inner K x y) / ‖x‖ := by
  rw [fderiv_norm (K := K) (E := E) hx]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The norming functional `reInnerSL K x` has operator norm `‖x‖` (it attains
`‖x‖` at `‖x‖⁻¹ • x`). -/
theorem norm_reInnerSL (x : E) : ‖reInnerSL K x‖ = ‖x‖ := by
  apply le_antisymm
  · calc ‖reInnerSL K x‖
        ≤ ‖RCLike.reCLM (K := K)‖ * ‖(innerSL K x).restrictScalars ℝ‖ :=
          (RCLike.reCLM (K := K)).opNorm_comp_le _
      _ ≤ 1 * ‖innerSL K x‖ := by
          rw [ContinuousLinearMap.norm_restrictScalars]
          gcongr
          exact (RCLike.reCLM (K := K)).opNorm_le_bound zero_le_one
            (fun z => by simpa using RCLike.norm_re_le_norm z)
      _ = ‖x‖ := by rw [one_mul, innerSL_apply_norm]
  · by_cases hx : x = 0
    · simp [hx]
    · have hxn : (‖x‖ : ℝ) ≠ 0 := (norm_pos_iff.mpr hx).ne'
      have h1 : ‖reInnerSL K x (‖x‖⁻¹ • x)‖ = ‖x‖ := by
        simp [reInnerSL_apply]
        field_simp
      have h2 : ‖reInnerSL K x (‖x‖⁻¹ • x)‖ ≤ ‖reInnerSL K x‖ * ‖‖x‖⁻¹ • x‖ :=
        (reInnerSL K x).le_opNorm _
      rw [h1] at h2
      have h3 : ‖‖x‖⁻¹ • x‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn]
      rw [h3, mul_one] at h2
      exact h2

/-- The Fréchet derivative of the norm at a nonzero point has operator norm `1`:
the norming functional is a norming functional. This statement needs the inner
product structure, so `K` is an explicit argument. -/
theorem norm_fderiv_norm (K : Type*) [RCLike K] [InnerProductSpace K E] {x : E}
    (hx : x ≠ 0) :
    ‖fderiv ℝ (fun y : E => ‖y‖) x‖ = 1 := by
  rw [fderiv_norm (K := K) (E := E) hx, norm_smul, norm_inv, norm_norm, norm_reInnerSL,
    inv_mul_cancel₀ (norm_pos_iff.mpr hx).ne']

/-- Over `ℝ`, the norming functional is just `innerSL ℝ x`. -/
theorem reInnerSL_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) : reInnerSL ℝ x = innerSL ℝ x := by
  ext y
  rfl

/-- The Fréchet derivative of the norm in a real inner product space. -/
theorem hasStrictFDerivAt_norm_real {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {x : E} (hx : x ≠ 0) :
    HasStrictFDerivAt (fun y : E => ‖y‖) ((‖x‖⁻¹ : ℝ) • innerSL ℝ x) x := by
  have h := hasStrictFDerivAt_norm (K := ℝ) (E := E) hx
  rwa [reInnerSL_real] at h

/-- The `fderiv` of the norm in a real inner product space, applied to a vector. -/
theorem fderiv_norm_apply_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y : E} (hx : x ≠ 0) :
    fderiv ℝ (fun z : E => ‖z‖) x y = inner ℝ x y / ‖x‖ := by
  have h := fderiv_norm_apply (K := ℝ) (E := E) hx (y := y)
  rw [show RCLike.re (inner ℝ x y) = inner ℝ x y from rfl] at h
  exact h

/-- Chain rule: the derivative of the norm of a differentiable map. -/
theorem HasStrictFDerivAt.norm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : G → E} {f' : G →L[ℝ] E} {x : G} (hf : HasStrictFDerivAt f f' x)
    (h0 : f x ≠ 0) :
    HasStrictFDerivAt (fun y => ‖f y‖)
      (((‖f x‖⁻¹ : ℝ) • reInnerSL K (f x)).comp f') x :=
  (hasStrictFDerivAt_norm (K := K) (E := E) h0).comp x hf

/-- Chain rule: the non-strict derivative of the norm of a differentiable map. -/
theorem HasFDerivAt.norm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : G → E} {f' : G →L[ℝ] E} {x : G} (hf : HasFDerivAt f f' x)
    (h0 : f x ≠ 0) :
    HasFDerivAt (fun y => ‖f y‖)
      (((‖f x‖⁻¹ : ℝ) • reInnerSL K (f x)).comp f') x :=
  (hasFDerivAt_norm (K := K) (E := E) h0).comp x hf

/-- The derivative of the norm along a curve is the normalized real inner product
of the position with the velocity. -/
theorem HasDerivAt.norm {f : ℝ → E} {f' : E} {t : ℝ} (hf : HasDerivAt f f' t)
    (h0 : f t ≠ 0) :
    HasDerivAt (fun t => ‖f t‖) (RCLike.re (inner K (f t) f') / ‖f t‖) t := by
  have h := (HasFDerivAt.norm (K := K) (E := E) hf.hasFDerivAt h0).hasDerivAt
  convert h using 1
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- A differentiable curve lying on the unit sphere has velocity orthogonal to
its position (in the real-inner-product sense). -/
theorem re_inner_self_deriv_eq_zero_of_forall_norm_eq_one {γ : ℝ → E}
    (hγ : Differentiable ℝ γ) (h1 : ∀ t, ‖γ t‖ = 1) (t : ℝ) :
    RCLike.re (inner K (γ t) (deriv γ t)) = 0 := by
  have h0 : γ t ≠ 0 := by
    intro h
    have h1t := h1 t
    rw [h, norm_zero] at h1t
    exact zero_ne_one h1t
  have h := (HasDerivAt.norm (K := K) (E := E) (hγ t).hasDerivAt h0)
  have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
  have heq : (fun t => ‖γ t‖) = fun _ => (1 : ℝ) := by
    funext s; exact h1 s
  have hderiv : deriv (fun t => ‖γ t‖) t = 0 := by
    rw [heq]; exact deriv_const t 1
  rw [h.deriv] at hderiv
  rw [h1 t] at hderiv
  simpa using hderiv

/-- The gradient of the squared distance to a point `a` is `2 • reInnerSL K (x - a)`. -/
theorem hasStrictFDerivAt_dist_sq {x a : E} :
    HasStrictFDerivAt (fun y : E => dist y a ^ 2) (2 • reInnerSL K (x - a)) x := by
  have h := (hasStrictFDerivAt_norm_sq (K := K) (E := E) (x - a)).comp x
    ((hasStrictFDerivAt_id x).sub (hasStrictFDerivAt_const a x))
  have hfun : (fun y : E => ‖y - a‖ ^ 2) = fun y => dist y a ^ 2 := by
    funext y; rw [dist_eq_norm]
  rw [← hfun]
  simpa using h

/-- The `fderiv` of the squared distance to a point, applied to a vector. -/
theorem fderiv_dist_sq_apply {x a y : E} :
    fderiv ℝ (fun z : E => dist z a ^ 2) x y = 2 * RCLike.re (inner K (x - a) y) := by
  rw [(hasStrictFDerivAt_dist_sq (K := K) (E := E) (x := x) (a := a)).hasFDerivAt.fderiv]
  simp only [smul_apply, reInnerSL_apply]
  rw [two_smul, two_mul]

omit [NormedSpace ℝ E] in
/-- The distance from `y` to a subspace with an orthogonal projection is the
norm of the residual `y - S.starProjection y`. -/
theorem infDist_eq_norm_sub_starProjection {S : Submodule K E} [S.HasOrthogonalProjection]
    (y : E) :
    Metric.infDist y (S : Set E) = ‖y - S.starProjection y‖ := by
  apply le_antisymm
  · exact (Metric.infDist_le_dist_of_mem (S.starProjection_apply_mem y)).trans_eq
      (dist_eq_norm y (S.starProjection y))
  · apply (Metric.le_infDist (s := (S : Set E)) ⟨0, S.zero_mem⟩).mpr
    intro w hw
    rw [dist_eq_norm, S.starProjection_minimal y]
    exact ciInf_le (f := fun x : ↥S => ‖y - (x : E)‖)
      ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ ⟨w, hw⟩

/-- The gradient of the squared residual `‖y - S.starProjection y‖ ^ 2` is
`2 • reInnerSL K (x - S.starProjection x)`, using that the residual operator
`1 - S.starProjection` is self-adjoint and idempotent. -/
theorem hasStrictFDerivAt_residual_sq {S : Submodule K E} [S.HasOrthogonalProjection]
    (x : E) :
    HasStrictFDerivAt (fun y : E => ‖y - S.starProjection y‖ ^ 2)
      (2 • reInnerSL K (x - S.starProjection x)) x := by
  set P : E →L[K] E := S.starProjection with hP
  have hg : HasStrictFDerivAt ⇑((1 - P : E →L[K] E).restrictScalars ℝ)
      ((1 - P : E →L[K] E).restrictScalars ℝ) x :=
    ((1 - P : E →L[K] E).restrictScalars ℝ).hasStrictFDerivAt
  have hcomp := (hasStrictFDerivAt_norm_sq (K := K) (E := E) ((1 - P) x)).comp x hg
  have hfun : (fun y : E => ‖(1 - P) y‖ ^ 2) = fun y => ‖y - P y‖ ^ 2 := by
    funext y
    simp [P, sub_apply, one_apply_eq_self]
  have hderiv : ((2 • reInnerSL K ((1 - P) x)).comp
        ((1 - P : E →L[K] E).restrictScalars ℝ))
      = 2 • reInnerSL K (x - P x) := by
    ext y
    have hPy : P y ∈ S := S.starProjection_apply_mem y
    have h0 : inner K (P y) (x - P x) = 0 :=
      inner_eq_zero_symm.mp (S.starProjection_inner_eq_zero x (P y) hPy)
    have h1 : inner K ((1 - P) x) (P y) = 0 := by
      rw [← inner_conj_symm]
      have hsub : (1 - P) x = x - P x := by
        simp [P, sub_apply, one_apply_eq_self]
      rw [hsub, h0]
      simp
    have key : RCLike.re (inner K ((1 - P) x) ((1 - P) y))
        = RCLike.re (inner K (x - P x) y) := by
      have hsuby : (1 - P) y = y - P y := by
        simp [P, sub_apply, one_apply_eq_self]
      have hsubx : (1 - P) x = x - P x := by
        simp [P, sub_apply, one_apply_eq_self]
      calc RCLike.re (inner K ((1 - P) x) ((1 - P) y))
          = RCLike.re (inner K ((1 - P) x) (y - P y)) := by rw [hsuby]
        _ = RCLike.re (inner K ((1 - P) x) y - inner K ((1 - P) x) (P y)) := by
            rw [inner_sub_right]
        _ = RCLike.re (inner K ((1 - P) x) y) := by rw [h1, sub_zero]
        _ = RCLike.re (inner K (x - P x) y) := by rw [hsubx]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      smul_apply, reInnerSL_apply, key]
  rw [← hfun, ← hderiv]
  exact hcomp

/-- The gradient of the squared distance to a subspace `S` is twice the real
inner product with the residual `x - S.starProjection x`. -/
theorem hasStrictFDerivAt_infDist_sq {S : Submodule K E} [S.HasOrthogonalProjection]
    (x : E) :
    HasStrictFDerivAt (fun y : E => Metric.infDist y (S : Set E) ^ 2)
      (2 • reInnerSL K (x - S.starProjection x)) x := by
  have hfun : (fun y : E => Metric.infDist y (S : Set E) ^ 2)
      = fun y => ‖y - S.starProjection y‖ ^ 2 := by
    funext y
    rw [infDist_eq_norm_sub_starProjection (S := S) (E := E)]
  rw [hfun]
  exact hasStrictFDerivAt_residual_sq (S := S) (E := E) x

end MathlibExt.Analysis.InnerProductSpace.NormDerivative
