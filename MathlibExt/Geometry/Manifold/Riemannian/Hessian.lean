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

/-- **Riemannian gradient.** Let $M$ be a $C^1$ manifold modelled on a complete real normed
space, with a Riemannian metric, and let $f : M \to \mathbb{R}$ and $x \in M$. The Riemannian
gradient $\operatorname{grad} f(x) = (df_x)^\sharp \in T_xM$ is the image of the differential
$df_x$ of $f$ at $x$ under the inverse of the Riesz isomorphism
$T_xM \to (T_xM)^*$, $w \mapsto \langle w, \cdot \rangle$, given by the metric at $x$. It is the
unique tangent vector with $\langle \operatorname{grad} f(x), v \rangle = df_x(v)$ for all
$v \in T_xM$. -/
def riemannianGradient (f : M → ℝ) (x : M) : TangentSpace I x :=
  (InnerProductSpace.toDual ℝ (TangentSpace I x)).symm (mvfderiv I f x)

/-- **Pairing of the Riemannian gradient with a tangent vector.** Let $M$ be a $C^1$ manifold
modelled on a complete real normed space, with a Riemannian metric $\langle \cdot, \cdot \rangle$,
and let $f : M \to \mathbb{R}$, $x \in M$ and $v \in T_xM$. Then
$\langle \operatorname{grad} f(x), v \rangle = df_x(v)$, where $\operatorname{grad} f(x)$ is the
Riemannian gradient of $f$ at $x$ and $df_x$ is the differential of $f$ at $x$. -/
@[simp]
theorem inner_riemannianGradient (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    inner ℝ (riemannianGradient I f x) v = (mvfderiv I f x) v :=
  InnerProductSpace.toDual_symm_apply

/-- **Characterization of the Riemannian gradient.** Let $M$ be a $C^1$ manifold modelled on a
complete real normed space, with a Riemannian metric $\langle \cdot, \cdot \rangle$, and let
$f : M \to \mathbb{R}$, $x \in M$ and $w \in T_xM$. Then the Riemannian gradient
$\operatorname{grad} f(x)$ equals $w$ if and only if $\langle w, v \rangle = df_x(v)$ for every
$v \in T_xM$, where $df_x$ is the differential of $f$ at $x$. -/
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

/-- **Norm of the Riemannian gradient.** Let $M$ be a $C^1$ manifold modelled on a complete real
normed space, with a Riemannian metric, and let $f : M \to \mathbb{R}$ and $x \in M$. With $T_xM$
normed by the metric at $x$, the norm of the Riemannian gradient $\operatorname{grad} f(x)$ equals
the operator norm of the differential $df_x : T_xM \to \mathbb{R}$ of $f$ at $x$:
$\|\operatorname{grad} f(x)\| = \|df_x\|$. This is the quantity $|\nabla f|(x)$. -/
theorem norm_riemannianGradient (f : M → ℝ) (x : M) :
    ‖riemannianGradient I f x‖ = ‖mvfderiv I f x‖ :=
  LinearIsometryEquiv.norm_map _ _

end Gradient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Covariant Hessian.** Let $M$ be a smooth manifold modelled on a finite-dimensional real
normed space, with a smooth Riemannian metric and its Levi-Civita connection $\nabla$. For
$f : M \to \mathbb{R}$, a point $x \in M$ and tangent vectors $u, v \in T_xM$, let $V$ be the
extension of $v$ to a vector field with constant coordinates in the preferred chart at $x$, so
that $V(x) = v$. The Hessian of $f$ at $x$ is the real number
$$\nabla^2 f(u, v) = d\big(y \mapsto df_y(V(y))\big)_x(u) - df_x(\nabla_u V),$$
that is, $u(Vf) - df_x(\nabla_u V)$, where $df_y$ is the differential of $f$ at $y$.

This is the textbook Hessian $\nabla^2 f = \nabla(df)$, $\nabla^2 f(u, v) = (\nabla_u df)(v)$
(Lee, *Introduction to Riemannian Manifolds*, 2nd ed., GTM 176, Ch. 4), provided the
Levi-Civita connection sends smooth vector fields to smooth vector fields. That regularity is a
standard fact that is not proved here, so the Hessian is defined as a function of two tangent
vectors rather than as a bilinear map. -/
def hessian (f : M → ℝ) (x : M) (u v : TangentSpace I x) : ℝ :=
  (mvfderiv I (fun y => (mvfderiv I f y) (FiberBundle.extend E v y)) x) u -
    (mvfderiv I f x)
      (CovariantDerivative.leviCivitaConnection I M (FiberBundle.extend E v) x u)

/-- **The Riemannian gradient on a Hilbert space.** Let $F$ be a real Hilbert space, viewed as
a Riemannian manifold with the metric given by its inner product, and let $f : F \to \mathbb{R}$
and $x \in F$. Identifying the tangent space at $x$ with $F$, the Riemannian gradient of $f$ at
$x$ is the Hilbert-space gradient $\nabla f(x)$, the unique vector with
$\langle \nabla f(x), w \rangle = Df(x)(w)$ for all $w \in F$, where $Df(x)$ is the Fréchet
derivative of $f$ at $x$. -/
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

/-- **The Hessian on Euclidean space as an iterated directional derivative.** Let $F$ be a
finite-dimensional real inner product space, viewed as a Riemannian manifold with the metric
given by its inner product, let $f : F \to \mathbb{R}$ and let $x \in F$. For all tangent vectors
$u, v$ at $x$, identified with vectors of $F$, the Hessian of $f$ at $x$ is the derivative at $x$
in direction $u$ of the function $y \mapsto Df(y)(v)$, where $Df(y)$ is the Fréchet derivative of
$f$ at $y$: $\nabla^2 f(u, v) = D\big(y \mapsto Df(y)(v)\big)(x)(u)$.

A Fréchet derivative that does not exist is taken to be $0$, so no hypothesis on $f$ is
needed. -/
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

/-- **The Hessian on Euclidean space is the second derivative.** Let $F$ be a finite-dimensional
real inner product space, viewed as a Riemannian manifold with the metric given by its inner
product, let $f : F \to \mathbb{R}$ and let $x \in F$. If the Fréchet derivative
$y \mapsto Df(y)$ of $f$ is differentiable at $x$, then for all tangent vectors $u, v$ at $x$,
identified with vectors of $F$, the Hessian of $f$ at $x$ is the second Fréchet derivative:
$\nabla^2 f(u, v) = D^2 f(x)(u)(v)$, where $D^2 f(x)$ is the derivative of $Df$ at $x$. -/
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
