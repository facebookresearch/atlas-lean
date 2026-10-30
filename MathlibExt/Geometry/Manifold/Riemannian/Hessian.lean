/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.Riemannian.VectorSpace
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Riemannian gradient and covariant Hessian of a function

Let `M` be a `C^∞` manifold with a `C^∞` Riemannian metric `g`, given as in
`Mathlib.Geometry.Manifold.Riemannian.Basic` by `IsManifold I ∞ M`,
`RiemannianBundle (fun x : M ↦ TangentSpace I x)` and
`IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)`, and let `∇` be its
Levi-Civita connection `CovariantDerivative.leviCivitaConnection I M`. We define the gradient
and Hessian of a function `f : M → ℝ`. The Hessian follows the conventions of Lee,
*Introduction to Riemannian Manifolds* (2nd ed., GTM 176, 2018), Ch. 4; the gradient is the
standard Riesz representative of the differential.

* `Manifold.riemannianGradient I f x`: the Riemannian gradient `grad f(x) = (df_x)^♯`, the
  inverse Riesz isomorphism applied to `mvfderiv I f x`.
* `Manifold.hessian I f x u v`: the covariant Hessian `∇²f(u, v) = (∇_u df)(v)`, computed from
  the extension `FiberBundle.extend E v`, as in `Manifold.riemannCurvature`.
* Vector-space specializations: on an inner product space the gradient is Mathlib's
  `gradient` and the Hessian is the iterated Fréchet derivative.

## Implementation notes

As for `Manifold.riemannCurvature`, the Hessian is computed pointwise from extensions of tangent
vectors to vector fields. This is the textbook Hessian because the Levi-Civita connection of a
`C^∞` metric is `C^∞`, so it sends the smooth extensions to smooth vector fields where it is
uniquely determined, and the Hessian expression is tensorial. Mathlib does not yet prove that
regularity (see the TODO in `LeviCivita.lean`); until it does, this agreement is a standard fact
not formalized here, and `hessian` is a function of its two tangent arguments rather than a
bundled bilinear map.

The gradient is stated under its minimal hypotheses: a `C^1` manifold structure and the metric,
with a complete model space. The Hessian keeps the `C^∞` block above since it uses
`leviCivitaConnection`.
-/

@[expose] public section

open Bundle
open scoped Manifold ContDiff

noncomputable section

namespace Manifold

section Gradient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The Riemannian gradient of `f : M → ℝ` at `x`: `grad f(x) = (df_x)^♯`, the inverse of the
Riesz isomorphism `InnerProductSpace.toDual ℝ (TangentSpace I x)` applied to the differential
`mvfderiv I f x`. It is the unique tangent vector with `inner grad v = df_x v` for all `v`. -/
def riemannianGradient (f : M → ℝ) (x : M) : TangentSpace I x :=
  (InnerProductSpace.toDual ℝ (TangentSpace I x)).symm (mvfderiv I f x)

/-- The metric inner product of the Riemannian gradient with `v` is the differential applied
to `v`. -/
@[simp]
theorem inner_riemannianGradient (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    inner ℝ (riemannianGradient I f x) v = (mvfderiv I f x) v :=
  InnerProductSpace.toDual_symm_apply

/-- Characterization of the Riemannian gradient: it equals `w` iff `w` pairs with every `v`
as the differential does. -/
theorem riemannianGradient_eq_iff (f : M → ℝ) (x : M) (w : TangentSpace I x) :
    riemannianGradient I f x = w ↔ ∀ v, inner ℝ w v = (mvfderiv I f x) v := by
  constructor
  · intro h v
    rw [← h]
    exact inner_riemannianGradient I f x v
  · intro h
    have heq : ∀ v, inner ℝ (riemannianGradient I f x) v = inner ℝ w v := by
      intro v
      exact (inner_riemannianGradient I f x v).trans (h v).symm
    have hsub : ∀ v, inner ℝ (riemannianGradient I f x - w) v = 0 := by
      intro v
      rw [inner_sub_left, heq v, sub_self]
    have h0 : inner ℝ (riemannianGradient I f x - w)
        (riemannianGradient I f x - w) = 0 :=
      hsub _
    have h_eq_zero : riemannianGradient I f x - w = 0 :=
      inner_self_eq_zero.mp h0
    exact sub_eq_zero.mp h_eq_zero

/-- The norm of the Riemannian gradient is the operator norm of the differential. This is the
quantity `|∇f|(x)`. -/
theorem norm_riemannianGradient (f : M → ℝ) (x : M) :
    ‖riemannianGradient I f x‖ = ‖mvfderiv I f x‖ :=
  LinearIsometryEquiv.norm_map _ _

end Gradient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The covariant Hessian of `f : M → ℝ` at `x`, as a function of two tangent vectors:
`∇²f(u, v) = (∇_u df)(v) = u(V f) - df_x(∇_u V)`, where `V` is any vector field with `V x = v`
and `∇` is the Levi-Civita connection. Here `V` is the extension `FiberBundle.extend E v`
(constant coordinates in the preferred chart at `x`), as in `Manifold.riemannCurvature`.

This is the textbook Hessian `∇²f = ∇(df)` (Lee, *Introduction to Riemannian Manifolds*,
2nd ed., GTM 176, Ch. 4; on Euclidean space it is the second derivative) because the
Levi-Civita connection of a `C^∞` metric is `C^∞`, so it sends the smooth extension to a smooth
vector field where it is uniquely determined and the Hessian expression is tensorial. Mathlib
does not yet prove that regularity (see the TODO in `LeviCivita.lean`); until it does, this
agreement is a standard fact not formalized here, and `hessian` is a function of its two tangent
arguments rather than a bundled bilinear map. -/
def hessian (f : M → ℝ) (x : M) (u v : TangentSpace I x) : ℝ :=
  (mvfderiv I (fun y => (mvfderiv I f y) (FiberBundle.extend E v y)) x) u -
    (mvfderiv I f x)
      (CovariantDerivative.leviCivitaConnection I M (FiberBundle.extend E v) x u)

/-- On an inner product space with its standard metric, the Riemannian gradient is Mathlib's
Hilbert-space `gradient`. Since `TangentSpace 𝓘(ℝ, F) x` is definitionally `F`, the equality
typechecks directly; the proof works in `F` through `NormedSpace.fromTangentSpace`. -/
theorem riemannianGradient_vectorSpace {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (f : F → ℝ) (x : F) :
    riemannianGradient 𝓘(ℝ, F) f x = gradient f x := by
  have hgrad : (InnerProductSpace.toDual ℝ F) (gradient f x) = fderiv ℝ f x :=
    toDual_gradient
  let g₀ : F :=
    (NormedSpace.fromTangentSpace x) (riemannianGradient 𝓘(ℝ, F) f x)
  have h_inner_t : ∀ v : TangentSpace 𝓘(ℝ, F) x,
      inner ℝ (riemannianGradient 𝓘(ℝ, F) f x) v = (mvfderiv 𝓘(ℝ, F) f x) v :=
    fun v => inner_riemannianGradient 𝓘(ℝ, F) f x v
  have h_mvfderiv : ∀ v : TangentSpace 𝓘(ℝ, F) x,
      (mvfderiv 𝓘(ℝ, F) f x) v = (fderiv ℝ f x)
        ((NormedSpace.fromTangentSpace x) v) := by
    intro v
    rw [mvfderiv_eq_fderiv]
    rfl
  have h_inner_f : ∀ v : TangentSpace 𝓘(ℝ, F) x,
      inner ℝ (riemannianGradient 𝓘(ℝ, F) f x) v =
        inner ℝ g₀ ((NormedSpace.fromTangentSpace x) v) :=
    fun v => rfl
  have h_dual : ∀ w : F, inner ℝ g₀ w = (fderiv ℝ f x) w := by
    intro w
    let v : TangentSpace 𝓘(ℝ, F) x := (w : TangentSpace 𝓘(ℝ, F) x)
    have h1 : inner ℝ g₀ ((NormedSpace.fromTangentSpace x) v) =
        (fderiv ℝ f x) ((NormedSpace.fromTangentSpace x) v) := by
      calc inner ℝ g₀ ((NormedSpace.fromTangentSpace x) v)
          = inner ℝ (riemannianGradient 𝓘(ℝ, F) f x) v := (h_inner_f v).symm
        _ = (mvfderiv 𝓘(ℝ, F) f x) v := h_inner_t v
        _ = (fderiv ℝ f x) ((NormedSpace.fromTangentSpace x) v) := h_mvfderiv v
    exact h1
  have h_grad : ∀ w : F, inner ℝ (gradient f x) w = (fderiv ℝ f x) w := by
    intro w
    rw [← InnerProductSpace.toDual_apply_apply, hgrad]
  have heq : ∀ w : F, inner ℝ g₀ w = inner ℝ (gradient f x) w :=
    fun w => (h_dual w).trans (h_grad w).symm
  have hsub : ∀ w : F, inner ℝ (g₀ - gradient f x) w = 0 := by
    intro w
    rw [inner_sub_left, heq w, sub_self]
  have h0 : inner ℝ (g₀ - gradient f x) (g₀ - gradient f x) = 0 := hsub _
  have h_eq_zero : g₀ - gradient f x = 0 := inner_self_eq_zero.mp h0
  have h_eq : g₀ = gradient f x := sub_eq_zero.mp h_eq_zero
  -- `NormedSpace.fromTangentSpace x` is the identity up to definitional unfolding of
  -- `TangentSpace 𝓘(ℝ, F) x` to `F`, so `g₀` is definitionally
  -- `riemannianGradient 𝓘(ℝ, F) f x` and `h_eq` closes the goal.
  exact h_eq

/-- On an inner product space, the Hessian is the derivative in direction `u` of
`y ↦ fderiv ℝ f y v`, with no hypothesis on `f`. Tangent vectors are identified with vectors
in `F` via `NormedSpace.fromTangentSpace`. -/
theorem hessian_vectorSpace {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (f : F → ℝ) (x : F) (u v : TangentSpace 𝓘(ℝ, F) x) :
    hessian 𝓘(ℝ, F) f x u v =
      fderiv ℝ (fun y => fderiv ℝ f y ((NormedSpace.fromTangentSpace x) v)) x
        ((NormedSpace.fromTangentSpace x) u) := by
  simp only [hessian, CovariantDerivative.leviCivitaConnection_extend_vectorSpace,
    zero_apply, map_zero, sub_zero]
  have h_fun : (fun y : F => (mvfderiv 𝓘(ℝ, F) f y) (FiberBundle.extend F v y)) =
      (fun y : F => fderiv ℝ f y ((NormedSpace.fromTangentSpace x) v)) := by
    funext y
    rw [FiberBundle.extend_model_space]
    rw [mvfderiv_eq_fderiv]
    rfl
  rw [h_fun]
  rw [mvfderiv_eq_fderiv]
  rfl

/-- On an inner product space, if `fderiv ℝ f` is differentiable at `x`, the Hessian is the
second Fréchet derivative. -/
theorem hessian_vectorSpace_eq_fderiv_fderiv {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (f : F → ℝ) (x : F)
    (u v : TangentSpace 𝓘(ℝ, F) x) (h : DifferentiableAt ℝ (fderiv ℝ f) x) :
    hessian 𝓘(ℝ, F) f x u v =
      (fderiv ℝ (fderiv ℝ f) x ((NormedSpace.fromTangentSpace x) u))
        ((NormedSpace.fromTangentSpace x) v) := by
  rw [hessian_vectorSpace]
  let u₀ : F := (NormedSpace.fromTangentSpace x) u
  let v₀ : F := (NormedSpace.fromTangentSpace x) v
  change (fderiv ℝ (fun y : F => (fderiv ℝ f y) v₀) x) u₀ =
    (fderiv ℝ (fderiv ℝ f) x u₀) v₀
  have h_const : DifferentiableAt ℝ (fun _ : F => v₀) x :=
    differentiableAt_const v₀
  have h_eq : fderiv ℝ (fun y : F => (fderiv ℝ f y) v₀) x =
      fderiv ℝ f x ∘SL fderiv ℝ (fun _ : F => v₀) x +
        (fderiv ℝ (fderiv ℝ f) x).flip v₀ :=
    fderiv_clm_apply h h_const
  have h_zero : fderiv ℝ (fun _ : F => v₀) x = 0 := fderiv_const_apply v₀
  rw [h_zero, ContinuousLinearMap.comp_zero, zero_add] at h_eq
  have h_apply := congrArg (fun L : F →L[ℝ] ℝ => L u₀) h_eq
  rw [ContinuousLinearMap.flip_apply] at h_apply
  exact h_apply

end Manifold
