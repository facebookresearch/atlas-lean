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

/-- On the tangent bundle of a normed space, the extension of a tangent vector `u` at `x` is the
constant vector field with value `u`. -/
theorem FiberBundle.extend_model_space (x : F) (u : TangentSpace 𝓘(𝕜, F) x) (y : F) :
    extend F u y = u := by
  have hy : y ∈ (trivializationAt F (TangentSpace 𝓘(𝕜, F)) x).baseSet := by simp
  simp only [extend]
  rw [← Trivialization.symmL_apply (R := 𝕜) _ hy, TangentBundle.symmL_model_space]
  simp only [trivializationAt_model_space_apply]
  rfl

/-- On a normed space, the extension of a tangent vector is differentiable at every point (not only
at the base point of the tangent vector). -/
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

/-- On a normed space, the Lie bracket of two constant vector fields `extend F a` and `extend F b`
vanishes. -/
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

/-- The Levi-Civita connection of an inner product space vanishes on constant vector fields. -/
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

/-- **Euclidean space is flat**: the Riemann curvature endomorphism of an inner product space,
with its standard metric `riemannianMetricVectorSpace`, vanishes. -/
theorem riemannCurvature_vectorSpace (x : F) (u v w : TangentSpace 𝓘(ℝ, F) x) :
    riemannCurvature 𝓘(ℝ, F) x u v w = 0 := by
  simp only [riemannCurvature, CovariantDerivative.extendCurvature,
    CovariantDerivative.leviCivitaConnection_extend_vectorSpace]
  have h0 : (fun y : F ↦ (0 : TangentSpace 𝓘(ℝ, F) y)) = 0 := rfl
  simp [h0]

/-- The sectional curvature of an inner product space vanishes. -/
theorem sectionalCurvature_vectorSpace (x : F) (u v : TangentSpace 𝓘(ℝ, F) x) :
    sectionalCurvature 𝓘(ℝ, F) x u v = 0 := by
  simp [sectionalCurvature, riemannCurvature_vectorSpace]

/-- The Ricci curvature of an inner product space vanishes. -/
theorem ricci_vectorSpace (x : F) (v w : TangentSpace 𝓘(ℝ, F) x) :
    ricci 𝓘(ℝ, F) x v w = 0 := by
  simp only [ricci, CovariantDerivative.extendRicci]
  simp [← riemannCurvature.eq_def, riemannCurvature_vectorSpace]

/-- The scalar curvature of an inner product space vanishes. -/
theorem scalarCurvature_vectorSpace (x : F) : scalarCurvature 𝓘(ℝ, F) x = 0 := by
  simp [scalarCurvature, ricci_vectorSpace]

end Manifold
