/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.Riemannian.Hessian
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Tests for the Riemannian gradient on `ℝ⁴`

Value, nonvanishing, norm and wrong-coefficient pins for `f x = ‖x‖ ^ 2 / 4` on the
concrete space `EuclideanSpace ℝ (Fin 4)` with model `𝓡 4`, at
`e₀ = EuclideanSpace.single 0 1`: the Riemannian gradient at `e₀` is `(1 / 2) • e₀`,
it is nonzero, its norm at `e₀` is `1 / 2`, and more generally `‖grad f x‖ = ‖x‖ / 2`
for every `x`. Each statement is computed through `riemannianGradient_vectorSpace`
and Mathlib's `gradient`, so a wrong definition would be caught.
-/

open Bundle Manifold
open scoped Manifold ContDiff

noncomputable section

namespace GradientTests

/-- Mathlib gradient of `‖x‖ ^ 2 / 4` on `ℝ⁴`: it equals `(1 / 2) • x`. -/
theorem gradient_normSq_div_four (x : EuclideanSpace ℝ (Fin 4)) :
    gradient (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x
      = (1 / 2 : ℝ) • x := by
  have hcont : ContDiff ℝ (∞ : ℕ∞ω)
      (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2) :=
    contDiff_norm_sq ℝ
  have hdiff : Differentiable ℝ
      (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2) :=
    hcont.differentiable (by simp)
  have hdiff_sq :
      DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2) x :=
    hdiff x
  have hhas : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2)
      (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2) x) x :=
    hdiff_sq.hasFDerivAt
  have hhas4 :
      HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 4) => (1 / 4 : ℝ) • ‖y‖ ^ 2)
        ((1 / 4 : ℝ) • fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2) x)
        x :=
    hhas.const_smul (1 / 4 : ℝ)
  have hfun_eq : (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4)
      = (fun y : EuclideanSpace ℝ (Fin 4) => (1 / 4 : ℝ) • ‖y‖ ^ 2) := by
    funext y
    rw [smul_eq_mul]
    ring
  have hfderiv : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x
      = (1 / 4 : ℝ) • fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2) x := by
    rw [hfun_eq]
    exact hhas4.fderiv
  have hgrad : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 4)))
        (gradient (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)
      = fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x :=
    toDual_gradient
  have htarget : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 4)))
        ((1 / 2 : ℝ) • x)
      = fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x := by
    rw [hfderiv, fderiv_norm_sq_apply]
    ext w
    simp [InnerProductSpace.toDual_apply_apply, smul_eq_mul]
    ring
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 4))).injective
    (hgrad.trans htarget.symm)

/-- The norm of `e₀ = EuclideanSpace.single 0 1` in `ℝ⁴` is `1`. -/
theorem single_norm :
    ‖EuclideanSpace.single (0 : Fin 4) (1 : ℝ)‖ = 1 := by
  simp

/-- The Riemannian gradient of `‖x‖ ^ 2 / 4` on `ℝ⁴` at `e₀` is `(1 / 2) • e₀`. -/
example : riemannianGradient (𝓡 4)
      (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 4)
      (EuclideanSpace.single (0 : Fin 4) (1 : ℝ))
    = (1 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 4) (1 : ℝ) := by
  have hR : riemannianGradient (𝓡 4)
        (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 4)
        (EuclideanSpace.single (0 : Fin 4) (1 : ℝ))
      = gradient (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 4)
        (EuclideanSpace.single (0 : Fin 4) (1 : ℝ)) :=
    riemannianGradient_vectorSpace _ _
  rw [hR, gradient_normSq_div_four]

/-- The Riemannian gradient of `‖x‖ ^ 2 / 4` at `e₀` is nonzero. -/
example : riemannianGradient (𝓡 4)
      (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 4)
      (EuclideanSpace.single (0 : Fin 4) (1 : ℝ)) ≠ 0 := by
  have hR : riemannianGradient (𝓡 4)
        (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 4)
        (EuclideanSpace.single (0 : Fin 4) (1 : ℝ))
      = gradient (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 4)
        (EuclideanSpace.single (0 : Fin 4) (1 : ℝ)) :=
    riemannianGradient_vectorSpace _ _
  rw [hR, gradient_normSq_div_four]
  intro hcon
  have hconF : (1 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 4) (1 : ℝ)
      = (0 : EuclideanSpace ℝ (Fin 4)) :=
    hcon
  have hn :=
    congrArg (fun v : EuclideanSpace ℝ (Fin 4) => ‖v‖) hconF
  simp only [norm_smul, single_norm, Real.norm_eq_abs, norm_zero] at hn
  norm_num at hn

/-- The norm of the Riemannian gradient is `‖x‖ / 2` for every `x : ℝ⁴`. -/
theorem norm_riemannianGradient_eq (x : EuclideanSpace ℝ (Fin 4)) :
    ‖riemannianGradient (𝓡 4)
        (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x‖ = ‖x‖ / 2 := by
  have hG : gradient (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x
      = (1 / 2 : ℝ) • x :=
    gradient_normSq_div_four x
  have hgradF : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 4)))
        (gradient (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)
      = fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x :=
    toDual_gradient
  have hfderiv : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x
      = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 4)))
        ((1 / 2 : ℝ) • x) := by
    rw [← hG]
    exact hgradF.symm
  have h_inner_t : ∀ v : TangentSpace (𝓡 4) x,
      inner ℝ (riemannianGradient (𝓡 4)
        (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x) v
        = (mvfderiv (𝓡 4)
          (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x) v :=
    fun v => inner_riemannianGradient _ _ _ v
  have h_inner_f : ∀ v : TangentSpace (𝓡 4) x,
      inner ℝ (riemannianGradient (𝓡 4)
        (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x) v
        = inner ℝ ((NormedSpace.fromTangentSpace x)
          (riemannianGradient (𝓡 4)
            (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x))
          ((NormedSpace.fromTangentSpace x) v) :=
    fun v => rfl
  have h_mvfderiv : ∀ v : TangentSpace (𝓡 4) x,
      (mvfderiv (𝓡 4) (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x) v
        = (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)
          ((NormedSpace.fromTangentSpace x) v) := by
    intro v
    rw [mvfderiv_eq_fderiv]
    rfl
  have hg₀ : (NormedSpace.fromTangentSpace x) (riemannianGradient (𝓡 4)
        (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)
      = (1 / 2 : ℝ) • x := by
    apply (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 4))).injective
    rw [← hfderiv]
    ext w
    simp only [InnerProductSpace.toDual_apply_apply]
    let v : TangentSpace (𝓡 4) x := (w : TangentSpace (𝓡 4) x)
    have h_from : (NormedSpace.fromTangentSpace x) v = w := rfl
    calc inner ℝ ((NormedSpace.fromTangentSpace x)
            (riemannianGradient (𝓡 4)
              (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)) w
          = inner ℝ ((NormedSpace.fromTangentSpace x)
            (riemannianGradient (𝓡 4)
              (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x))
            ((NormedSpace.fromTangentSpace x) v) := by rw [← h_from]
        _ = inner ℝ (riemannianGradient (𝓡 4)
            (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x) v :=
          (h_inner_f v).symm
        _ = (mvfderiv (𝓡 4)
            (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x) v :=
          h_inner_t v
        _ = (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)
            ((NormedSpace.fromTangentSpace x) v) := h_mvfderiv v
        _ = (fderiv ℝ
            (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x) w := by
          rw [h_from]
  have h_n : ‖riemannianGradient (𝓡 4)
        (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x‖
      = √(inner ℝ (riemannianGradient (𝓡 4)
        (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)
        (riemannianGradient (𝓡 4)
          (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)) :=
    norm_eq_sqrt_real_inner _
  have h_i : inner ℝ (riemannianGradient (𝓡 4)
        (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)
        (riemannianGradient (𝓡 4)
          (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)
      = (mvfderiv (𝓡 4) (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)
        (riemannianGradient (𝓡 4)
          (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x) :=
    inner_riemannianGradient _ _ _ _
  have h_m : (mvfderiv (𝓡 4)
        (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)
        (riemannianGradient (𝓡 4)
          (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)
      = (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)
        ((1 / 2 : ℝ) • x) := by
    rw [h_mvfderiv _, hg₀]
  have h_f : (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)
        ((1 / 2 : ℝ) • x)
      = inner ℝ ((1 / 2 : ℝ) • x) ((1 / 2 : ℝ) • x) := by
    rw [hfderiv, InnerProductSpace.toDual_apply_apply]
  have hE : ‖((1 / 2 : ℝ) • x : EuclideanSpace ℝ (Fin 4))‖
      = √(inner ℝ ((1 / 2 : ℝ) • x) ((1 / 2 : ℝ) • x)) :=
    norm_eq_sqrt_real_inner _
  calc ‖riemannianGradient (𝓡 4)
          (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x‖
        = √(inner ℝ (riemannianGradient (𝓡 4)
          (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)
          (riemannianGradient (𝓡 4)
            (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)) := h_n
      _ = √((mvfderiv (𝓡 4)
          (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)
          (riemannianGradient (𝓡 4)
            (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)) := by
        rw [h_i]
      _ = √((fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 4) => ‖y‖ ^ 2 / 4) x)
          ((1 / 2 : ℝ) • x)) := by rw [h_m]
      _ = √(inner ℝ ((1 / 2 : ℝ) • x) ((1 / 2 : ℝ) • x)) := by rw [h_f]
      _ = ‖((1 / 2 : ℝ) • x : EuclideanSpace ℝ (Fin 4))‖ := hE.symm
      _ = ‖x‖ / 2 := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        ring

/-- The norm of the Riemannian gradient at `e₀` is `1 / 2`. -/
example : ‖riemannianGradient (𝓡 4)
      (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 4)
      (EuclideanSpace.single (0 : Fin 4) (1 : ℝ))‖ = 1 / 2 := by
  rw [norm_riemannianGradient_eq, single_norm]

/-- Wrong-coefficient control: the gradient at `e₀` is not `e₀`. -/
example : riemannianGradient (𝓡 4)
      (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 4)
      (EuclideanSpace.single (0 : Fin 4) (1 : ℝ))
    ≠ EuclideanSpace.single (0 : Fin 4) (1 : ℝ) := by
  intro hcon
  have hR : riemannianGradient (𝓡 4)
        (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 4)
        (EuclideanSpace.single (0 : Fin 4) (1 : ℝ))
      = gradient (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖ ^ 2 / 4)
        (EuclideanSpace.single (0 : Fin 4) (1 : ℝ)) :=
    riemannianGradient_vectorSpace _ _
  rw [hR, gradient_normSq_div_four] at hcon
  have hconF : (1 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 4) (1 : ℝ)
      = EuclideanSpace.single (0 : Fin 4) (1 : ℝ) :=
    hcon
  have hn :=
    congrArg (fun v : EuclideanSpace ℝ (Fin 4) => ‖v‖) hconF
  simp only [norm_smul, single_norm, Real.norm_eq_abs, mul_one] at hn
  norm_num at hn

end GradientTests
