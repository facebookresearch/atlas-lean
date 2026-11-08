/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.Riemannian.Hessian
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import MathlibExt.Analysis.InnerProductSpace.NormSqHessian

/-!
# Laplace-Beltrami operator of a Riemannian manifold

Let `M` be a `C^∞` manifold with a `C^∞` Riemannian metric, in the setting of
`Manifold.hessian`, with Levi-Civita connection `∇`. We define the Laplace-Beltrami
operator as the metric trace of the covariant Hessian. On a finite-dimensional real
inner product space we compute it on the squared norm and on a Gaussian potential.

## Relationship to Mathlib's flat Laplacian

Mathlib already defines the flat Laplacian `Δ` on a finite-dimensional real inner
product space (`Laplacian.laplacian`, instance `InnerProductSpace.instLaplacian`,
notation `Δ` after `open Laplacian`, in `Mathlib.Analysis.InnerProductSpace.Laplacian`):
the trace of the second derivative over an orthonormal basis, with the same sign
convention as here. What is new here is the manifold (Laplace-Beltrami) operator
`Manifold.laplacian`. On the model space `𝓘(ℝ, F)`, under
`DifferentiableAt ℝ (fderiv ℝ f) x`, the new operator agrees with Mathlib's `Δ`
(same trace over the transferred `stdOrthonormalBasis`, same sign); see
`laplacian_vectorSpace_eq_laplacian`. Under that same hypothesis the vector-space
formulas below coincide with that flat Laplacian, not new operators.

## Main results

* `Manifold.laplacian I f x`: `Δf(x) = ∑ i, hessian I f x (e i) (e i)`.
* `Manifold.laplacian_vectorSpace`: on an inner product space this is the sum of the
  second directional derivatives from `Manifold.hessian_vectorSpace`.
* `Manifold.laplacian_vectorSpace_eq_laplacian`: under `DifferentiableAt` of
  `fderiv ℝ f` at `x`, this agrees with Mathlib's `Δ` on the model space.
* `Manifold.laplacian_norm_sq`: `Δ` of `‖·‖ ^ 2` is `2 * finrank ℝ F`.
* `Manifold.laplacian_gaussian`: `Δ` of `(a / 2) * ‖·‖ ^ 2` is `a * finrank ℝ F`.
-/

@[expose] public section

open Bundle
open Laplacian
open scoped Manifold ContDiff

noncomputable section

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The Laplace-Beltrami operator applied to `f : M → ℝ` at `x`: `Δf(x)` is the metric
trace `∑ i, hessian I f x (e i) (e i)` over the orthonormal basis
`e = stdOrthonormalBasis ℝ (TangentSpace I x)`, the same basis convention as
`Manifold.scalarCurvature`. For the textbook Hessian, which is bilinear, this trace
does not depend on the orthonormal basis; the regularity caveat of `Manifold.hessian`
applies here unchanged.

Sign convention `Δf = tr_g ∇²f`, the convention `Δ = div ∘ grad` under which `Δ` is the
sum `∑ ∂²/∂x_i²` on Euclidean space and `Δ(‖x‖²) = 2n`; the operator `-Δ` is then the
nonnegative one, and the opposite sign convention is also common. The identity
`Δ = div ∘ grad` is not proved here since no divergence is defined. Reference with the
same conventions: Lee, Introduction to Riemannian Manifolds (2nd ed., GTM 176).

Mathlib's flat Laplacian is `Laplacian.laplacian` (instance
`InnerProductSpace.instLaplacian`, notation `Δ` after `open Laplacian`): the trace of
the second derivative over an orthonormal basis of a finite-dimensional real inner
product space. On the model space `𝓘(ℝ, F)`, under
`DifferentiableAt ℝ (fderiv ℝ f) x`, this operator agrees with Mathlib's `Δ`
(same orthonormal-basis trace, same sign); see `laplacian_vectorSpace_eq_laplacian`
for the proved agreement. What is new here is the manifold operator itself. -/
def laplacian (f : M → ℝ) (x : M) : ℝ :=
  ∑ i, hessian I f x (stdOrthonormalBasis ℝ (TangentSpace I x) i)
    (stdOrthonormalBasis ℝ (TangentSpace I x) i)

/-- On a finite-dimensional real inner product space with its standard metric, the
Laplacian is the sum over the same orthonormal basis of the second directional
derivatives from `Manifold.hessian_vectorSpace`. The sum on the right is the
flat-Laplacian formula also computed by Mathlib's `Δ` (`Laplacian.laplacian`);
under `DifferentiableAt ℝ (fderiv ℝ f) x` the two operators agree, proved in
`laplacian_vectorSpace_eq_laplacian`. -/
theorem laplacian_vectorSpace {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (f : F → ℝ) (x : F) :
    laplacian 𝓘(ℝ, F) f x =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ f y
        ((NormedSpace.fromTangentSpace x)
          (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i))) x
        ((NormedSpace.fromTangentSpace x)
          (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)) := by
  unfold laplacian
  exact Finset.sum_congr rfl (fun i _ => hessian_vectorSpace f x _ _)

/-- On a finite-dimensional real inner product space, if `fderiv ℝ f` is differentiable
at `x`, the manifold Laplacian on the model space agrees with Mathlib's flat Laplacian
`Δ` (`Laplacian.laplacian`). The hypothesis is the one used by
`hessian_vectorSpace_eq_fderiv_fderiv`: Mathlib's `Δ f x` is built from
`fderiv ℝ (fderiv ℝ f) x`, which is `0` when `fderiv ℝ f` is not differentiable at `x`,
while `laplacian 𝓘(ℝ, F) f x` sums the directional derivatives of
`y ↦ fderiv ℝ f y v`. The orthonormal basis of `F` is the transfer of
`stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)` along `NormedSpace.fromTangentSpace x`,
which preserves inner products by `rfl`. -/
theorem laplacian_vectorSpace_eq_laplacian {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (f : F → ℝ) (x : F)
    (h : DifferentiableAt ℝ (fderiv ℝ f) x) :
    laplacian 𝓘(ℝ, F) f x = Δ f x := by
  have hpres : ∀ u v : TangentSpace 𝓘(ℝ, F) x,
      inner ℝ ((NormedSpace.fromTangentSpace x).toLinearEquiv u)
        ((NormedSpace.fromTangentSpace x).toLinearEquiv v) = inner ℝ u v :=
    fun u v => rfl
  let hL : TangentSpace 𝓘(ℝ, F) x ≃ₗᵢ[ℝ] F :=
    LinearEquiv.isometryOfInner (NormedSpace.fromTangentSpace x).toLinearEquiv hpres
  let hb : OrthonormalBasis (Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x))) ℝ F :=
    (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)).map hL
  have hv : ∀ i, ((stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)).map hL) i
      = (NormedSpace.fromTangentSpace x)
        ((stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)) i) := by
    intro i
    have h0 : ((stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)).map hL) i
        = hL ((stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)) i) :=
      OrthonormalBasis.map_apply
        (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)) hL i
    have h1 : hL ((stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)) i)
        = (NormedSpace.fromTangentSpace x)
          ((stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)) i) := rfl
    exact h0.trans h1
  have hLap : Δ f = fun y => ∑ i, iteratedFDeriv ℝ 2 f y ![hb i, hb i] :=
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f hb
  have hpoint : Δ f x = ∑ i, iteratedFDeriv ℝ 2 f x ![hb i, hb i] :=
    congrFun hLap x
  have hiter : ∀ i, (iteratedFDeriv ℝ 2 f x) ![hb i, hb i]
        = (fderiv ℝ (fderiv ℝ f) x (hb i)) (hb i) := by
    intro i
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hDelta : Δ f x = ∑ i, (fderiv ℝ (fderiv ℝ f) x (hb i)) (hb i) :=
    hpoint.trans (Finset.sum_congr rfl (fun i _ => hiter i))
  have hterm : ∀ i, fderiv ℝ (fun y => fderiv ℝ f y
        ((NormedSpace.fromTangentSpace x)
          ((stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)) i))) x
        ((NormedSpace.fromTangentSpace x)
          ((stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)) i))
      = (fderiv ℝ (fderiv ℝ f) x (hb i)) (hb i) := by
    intro i
    have h1 := hessian_vectorSpace f x
      ((stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)) i)
      ((stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)) i)
    have h2 := hessian_vectorSpace_eq_fderiv_fderiv f x
      ((stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)) i)
      ((stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)) i) h
    rw [hv i]
    exact h1.symm.trans h2
  calc laplacian 𝓘(ℝ, F) f x
      = ∑ i, fderiv ℝ (fun y => fderiv ℝ f y
          ((NormedSpace.fromTangentSpace x)
            ((stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)) i))) x
          ((NormedSpace.fromTangentSpace x)
            ((stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)) i)) :=
          laplacian_vectorSpace f x
    _ = ∑ i, (fderiv ℝ (fderiv ℝ f) x (hb i)) (hb i) :=
          Finset.sum_congr rfl (fun i _ => hterm i)
    _ = Δ f x := hDelta.symm

/-- The Laplacian of the squared norm on a finite-dimensional real inner product space
is `2 * finrank ℝ F` at every point. The Hessian of `‖·‖ ^ 2` is `2⟪·, ·⟫` by
`fderiv_fderiv_norm_sq_apply`, and each orthonormal basis vector pairs to one. These are
the familiar flat-space values, with the same sign convention as Mathlib's `Δ`. -/
theorem laplacian_norm_sq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (x : F) :
    laplacian 𝓘(ℝ, F) (fun x => ‖x‖ ^ 2) x
      = 2 * (Module.finrank ℝ F : ℝ) := by
  have hcontTop : ContDiff ℝ ⊤ (fun x : F ↦ ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  have hcontD : ContDiff ℝ ∞ (fderiv ℝ (fun x : F ↦ ‖x‖ ^ 2)) :=
    hcontTop.fderiv_right le_top
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (fun x : F ↦ ‖x‖ ^ 2)) x :=
    (hcontD.differentiable (by simp)) x
  have h_orth : ∀ i, inner ℝ
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) = 1 :=
    fun i => (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)).inner_eq_one i
  have h_bridge : ∀ i, inner ℝ
      ((NormedSpace.fromTangentSpace x)
        (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i))
      ((NormedSpace.fromTangentSpace x)
        (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)) =
      inner ℝ (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
        (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) := fun i => rfl
  have h_each : ∀ i, hessian 𝓘(ℝ, F) (fun x : F ↦ ‖x‖ ^ 2) x
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) = 2 := by
    intro i
    have h_hess := hessian_vectorSpace_eq_fderiv_fderiv
      (fun x : F ↦ ‖x‖ ^ 2) x
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) hdiff
    rw [h_hess, fderiv_fderiv_norm_sq_apply, h_bridge i, h_orth i, mul_one]
  have h_sum : (∑ i, hessian 𝓘(ℝ, F) (fun x : F ↦ ‖x‖ ^ 2) x
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)) =
      ∑ _ : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x)), (2 : ℝ) :=
    Finset.sum_congr rfl (fun i _ => h_each i)
  have h_card : (∑ _ : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x)), (2 : ℝ))
      = 2 * (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x) : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_comm]
  calc laplacian 𝓘(ℝ, F) (fun x : F ↦ ‖x‖ ^ 2) x
      = ∑ _ : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x)), (2 : ℝ) := by
        unfold laplacian
        exact h_sum
    _ = 2 * (Module.finrank ℝ F : ℝ) := h_card

/-- The Laplacian of the Gaussian potential `x ↦ (a / 2) * ‖x‖ ^ 2` on a
finite-dimensional real inner product space is `a * finrank ℝ F`. This is the
potential of the Gaussian gradient Ricci soliton. Each Hessian diagonal entry is `a`
since the second derivative is scaled by `a / 2` from the squared-norm case. As above,
this is the flat-space value with the same sign convention as Mathlib's `Δ`. -/
theorem laplacian_gaussian {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (a : ℝ) (x : F) :
    laplacian 𝓘(ℝ, F) (fun x => (a / 2) * ‖x‖ ^ 2) x
      = a * (Module.finrank ℝ F : ℝ) := by
  have hcontTop : ContDiff ℝ ⊤ (fun x : F ↦ ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  have hnorm_at : ∀ y, DifferentiableAt ℝ (fun x : F ↦ ‖x‖ ^ 2) y :=
    fun y => (hcontTop.differentiable (by simp)) y
  have hcontD : ContDiff ℝ ∞ (fderiv ℝ (fun x : F ↦ ‖x‖ ^ 2)) :=
    hcontTop.fderiv_right le_top
  have hdiff_norm : DifferentiableAt ℝ (fderiv ℝ (fun x : F ↦ ‖x‖ ^ 2)) x :=
    (hcontD.differentiable (by simp)) x
  have h_gsmul_eq : (fun x : F ↦ (a / 2) * ‖x‖ ^ 2)
      = (fun x : F ↦ (a / 2) • ‖x‖ ^ 2) := by
    funext y
    rw [smul_eq_mul]
  have h_g_fderiv : fderiv ℝ (fun x : F ↦ (a / 2) • ‖x‖ ^ 2)
      = fun y => (a / 2) • fderiv ℝ (fun x : F ↦ ‖x‖ ^ 2) y := by
    funext y
    exact fderiv_fun_const_smul (hnorm_at y) (a / 2)
  have h_g_diff : DifferentiableAt ℝ
      (fderiv ℝ (fun x : F ↦ (a / 2) • ‖x‖ ^ 2)) x := by
    rw [h_g_fderiv]
    exact hdiff_norm.const_smul (a / 2)
  have h_second : fderiv ℝ
      (fun y => (a / 2) • fderiv ℝ (fun x : F ↦ ‖x‖ ^ 2) y) x
      = (a / 2) • fderiv ℝ (fderiv ℝ (fun x : F ↦ ‖x‖ ^ 2)) x :=
    fderiv_fun_const_smul hdiff_norm (a / 2)
  have h_orth : ∀ i, inner ℝ
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) = 1 :=
    fun i => (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)).inner_eq_one i
  have h_bridge : ∀ i, inner ℝ
      ((NormedSpace.fromTangentSpace x)
        (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i))
      ((NormedSpace.fromTangentSpace x)
        (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)) =
      inner ℝ (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
        (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) := fun i => rfl
  have h_each : ∀ i, hessian 𝓘(ℝ, F) (fun x : F ↦ (a / 2) • ‖x‖ ^ 2) x
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) = a := by
    intro i
    have h_hess := hessian_vectorSpace_eq_fderiv_fderiv
      (fun x : F ↦ (a / 2) • ‖x‖ ^ 2) x
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) h_g_diff
    rw [h_hess, h_g_fderiv, h_second, smul_apply,
      smul_apply, fderiv_fderiv_norm_sq_apply, h_bridge i,
      h_orth i, mul_one, smul_eq_mul]
    ring
  have h_sum : (∑ i, hessian 𝓘(ℝ, F) (fun x : F ↦ (a / 2) • ‖x‖ ^ 2) x
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)) =
      ∑ _ : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x)), (a : ℝ) :=
    Finset.sum_congr rfl (fun i _ => h_each i)
  have h_card : (∑ _ : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x)), (a : ℝ))
      = a * (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x) : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_comm]
  rw [h_gsmul_eq]
  calc laplacian 𝓘(ℝ, F) (fun x : F ↦ (a / 2) • ‖x‖ ^ 2) x
      = ∑ _ : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ, F) x)), (a : ℝ) := by
        unfold laplacian
        exact h_sum
    _ = a * (Module.finrank ℝ F : ℝ) := h_card

end Manifold
