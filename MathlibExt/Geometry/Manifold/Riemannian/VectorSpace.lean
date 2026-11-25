/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import MathlibExt.Geometry.Manifold.Riemannian.Curvature

/-!
# Euclidean space is flat

An inner product space `F`, with the Riemannian metric `riemannianMetricVectorSpace F` given by the
inner product of `F` on every tangent space, is a flat Riemannian manifold: its Riemann curvature
endomorphism vanishes, together with the sectional, Ricci and scalar curvatures. The
`IsContMDiffRiemannianBundle` instance for this metric is Mathlib's
`Bundle.instIsContMDiffRiemannianBundle` applied to `riemannianMetricVectorSpace F`.

## Main results

* `FiberBundle.extend_model_space`: on the tangent bundle of a normed space, the extension
  `extend F u` of a tangent vector `u` is the constant vector field `u`.
* `CovariantDerivative.leviCivitaConnection_extend_vectorSpace`: the Levi-Civita connection of
  `F` vanishes on constant vector fields. The proof is the Koszul formula: all inner products of
  constant vector fields are constant and all their Lie brackets vanish.
* `Manifold.riemannCurvature_vectorSpace`: the Riemann curvature endomorphism of `F` is zero.
-/

@[expose] public section

open Bundle FiberBundle VectorField
open scoped Manifold ContDiff

noncomputable section

section NormedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Extending a tangent vector of a normed space gives a constant vector field.** Let $F$ be a
normed space over a nontrivially normed field, viewed as a manifold modelled on itself, so that
each tangent space of $F$ is $F$. For every point $x \in F$, tangent vector $u \in T_xF$ and point
$y \in F$, the extension of $u$ to a vector field on $F$ (built from the trivialization of the
tangent bundle at $x$) has value $u$ at $y$. -/
theorem FiberBundle.extend_model_space (x : F) (u : TangentSpace 𝓘(𝕜, F) x) (y : F) :
    extend F u y = u := by
  have hy : y ∈ (trivializationAt F (TangentSpace 𝓘(𝕜, F)) x).baseSet := by simp
  simp only [extend]
  rw [← Trivialization.symmL_apply (R := 𝕜) _ hy, TangentBundle.symmL_model_space]
  simp only [trivializationAt_model_space_apply]
  rfl

/-- **Extensions of tangent vectors of a normed space are differentiable.** Let $F$ be a normed
space over a nontrivially normed field, viewed as a manifold modelled on itself. For every point
$x \in F$, tangent vector $u \in T_xF$ and point $y \in F$, the extension of $u$ to a vector field
on $F$ (built from the trivialization of the tangent bundle at $x$), viewed as a map from $F$ to
its tangent bundle, is differentiable at $y$, not only at the base point $x$. -/
theorem FiberBundle.mdifferentiableAt_extend_model_space {x : F} (u : TangentSpace 𝓘(𝕜, F) x)
    (y : F) : MDiffAt (T% (extend F u)) y := by
  have h : extend F u = extend F (show TangentSpace 𝓘(𝕜, F) y from u) := by
    funext z; rw [extend_model_space x u z, extend_model_space y _ z]
  rw [h]
  exact mdifferentiableAt_extend 𝓘(𝕜, F) F _

private theorem lieBracketWithin_univ_of_forall_eq {V W : F → F} {a b : F}
    (hV : ∀ z, V z = a) (hW : ∀ z, W z = b) (y : F) :
    lieBracketWithin 𝕜 V W Set.univ y = 0 := by
  obtain rfl : V = fun _ ↦ a := funext hV
  obtain rfl : W = fun _ ↦ b := funext hW
  simp [lieBracketWithin_univ, lieBracket_eq]

/-- **Lie brackets of extended tangent vectors of a normed space vanish.** Let $F$ be a normed
space over a nontrivially normed field, viewed as a manifold modelled on itself. For points
$x, x' \in F$ and tangent vectors $a \in T_xF$ and $b \in T_{x'}F$, let $X$ and $Y$ be the
extensions of $a$ and $b$ to vector fields on $F$ (built from the trivializations of the tangent
bundle at $x$ and at $x'$). Then the Lie bracket $[X, Y]$ vanishes at every point $y \in F$. -/
theorem VectorField.mlieBracket_extend_model_space {x x' : F} (a : TangentSpace 𝓘(𝕜, F) x)
    (b : TangentSpace 𝓘(𝕜, F) x') (y : F) :
    mlieBracket 𝓘(𝕜, F) (extend F a) (extend F b) y = 0 := by
  rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin]
  exact lieBracketWithin_univ_of_forall_eq (extend_model_space x a) (extend_model_space x' b) y

end NormedSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private theorem inner_extend_model_space {x x' : F} (a : TangentSpace 𝓘(ℝ, F) x)
    (b : TangentSpace 𝓘(ℝ, F) x') :
    (fun y : F ↦ inner ℝ (extend F a y) (extend F b y)) = fun _ ↦ inner ℝ (a : F) (b : F) := by
  funext y
  rw [extend_model_space, extend_model_space]
  rfl

variable [FiniteDimensional ℝ F]

/-- **The Levi-Civita connection of Euclidean space kills constant vector fields.** Let $F$ be a
finite-dimensional real inner product space with the Riemannian metric given by its inner product
on every tangent space, and let $\nabla$ be its Levi-Civita connection. For every point $x \in F$
and tangent vector $w \in T_xF$, let $W$ be the extension of $w$ to a vector field on $F$ (built
from the trivialization of the tangent bundle at $x$; it is the constant vector field with value
$w$). Then the covariant derivative $\nabla W$ at every point $y \in F$ is the zero map. -/
theorem CovariantDerivative.leviCivitaConnection_extend_vectorSpace {x : F}
    (w : TangentSpace 𝓘(ℝ, F) x) (y : F) :
    leviCivitaConnection 𝓘(ℝ, F) F (extend F w) y = 0 := by
  ext X₀
  set c := leviCivitaConnection 𝓘(ℝ, F) F (extend F w) y X₀ with hc
  have key := leviCivitaConnection_apply_inner 𝓘(ℝ, F) (x := y)
    (X := extend F X₀) (Y := extend F w) (Z := extend F c)
    (mdifferentiableAt_extend_model_space ..) (mdifferentiableAt_extend_model_space ..)
    (mdifferentiableAt_extend_model_space ..)
  simp only [extend_apply_self, mlieBracket_extend_model_space, inner_extend_model_space,
    mvfderiv_const, inner_zero_right] at key
  rw [← hc] at key
  simpa using key

namespace Manifold

/-- **Euclidean space is flat.** Let $F$ be a finite-dimensional real inner product space with the
Riemannian metric given by its inner product on every tangent space. For every point $x \in F$
and all tangent vectors $u, v, w \in T_xF$, the Riemann curvature endomorphism $R$ of $F$ at $x$
satisfies $R(u, v)w = 0$. -/
theorem riemannCurvature_vectorSpace (x : F) (u v w : TangentSpace 𝓘(ℝ, F) x) :
    riemannCurvature 𝓘(ℝ, F) x u v w = 0 := by
  simp only [riemannCurvature, CovariantDerivative.extendCurvature,
    CovariantDerivative.leviCivitaConnection_extend_vectorSpace]
  have h0 : (fun y : F ↦ (0 : TangentSpace 𝓘(ℝ, F) y)) = 0 := rfl
  simp [h0]

/-- **Euclidean space has zero sectional curvature.** Let $F$ be a finite-dimensional real inner
product space with the Riemannian metric given by its inner product on every tangent space. For
every point $x \in F$ and all tangent vectors $u, v \in T_xF$, the sectional curvature $K(u, v)$
of $F$ at $x$ is $0$. -/
theorem sectionalCurvature_vectorSpace (x : F) (u v : TangentSpace 𝓘(ℝ, F) x) :
    sectionalCurvature 𝓘(ℝ, F) x u v = 0 := by
  simp [sectionalCurvature, riemannCurvature_vectorSpace]

/-- **Euclidean space is Ricci-flat.** Let $F$ be a finite-dimensional real inner product space
with the Riemannian metric given by its inner product on every tangent space. For every point
$x \in F$ and all tangent vectors $v, w \in T_xF$, the Ricci curvature $\mathrm{Ric}(v, w)$ of $F$
at $x$ is $0$. -/
theorem ricci_vectorSpace (x : F) (v w : TangentSpace 𝓘(ℝ, F) x) :
    ricci 𝓘(ℝ, F) x v w = 0 := by
  simp only [ricci, CovariantDerivative.extendRicci]
  simp [← riemannCurvature.eq_def, riemannCurvature_vectorSpace]

/-- **Euclidean space has zero scalar curvature.** Let $F$ be a finite-dimensional real inner
product space with the Riemannian metric given by its inner product on every tangent space. For
every point $x \in F$, the scalar curvature of $F$ at $x$ is $0$. -/
theorem scalarCurvature_vectorSpace (x : F) : scalarCurvature 𝓘(ℝ, F) x = 0 := by
  simp [scalarCurvature, ricci_vectorSpace]

end Manifold
