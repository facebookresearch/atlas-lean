/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.Riemannian.Hessian
import MathlibExt.Analysis.InnerProductSpace.NormSqHessian

/-!
# Gradient Ricci solitons

Let `(M, g)` be a `C^∞` Riemannian manifold as in `Manifold.ricci`. A gradient Ricci
soliton is a smooth potential `f : M → ℝ` and a constant `c : ℝ` with `Ric + Hess f`
equal to `c • g`.

* `Manifold.IsGradientRicciSoliton I f c`: `f` is `C^∞` and `Ric + Hess f = c • g`.
* `Manifold.IsGradientShrinkingRicciSoliton I f c`: a soliton with `0 < c`.
* Gaussian solitons on a finite-dimensional inner product space.

References: Oberwolfach Report 27/2012 (Geometrie): T. Yokota, p. 1651, defines a
gradient shrinking Ricci soliton by `Ric(g) + Hess f = g / (2 * λ)` with `λ > 0` and
`f` smooth; R. Haslhofer (with R. Müller), p. 1669, eq. (1), uses `Rc + Hess f = g / 2`.
-/

@[expose] public section

open Bundle
open scoped Manifold ContDiff

noncomputable section

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- A gradient Ricci soliton on `(M, g)`: a smooth potential `f` and constant `c` with
`Ric + Hess f = c • g`, where `Ric` is `Manifold.ricci` and `Hess` is `Manifold.hessian`.
This follows Oberwolfach Report 27/2012 (Geometrie): T. Yokota, p. 1651, defines a
gradient shrinking Ricci soliton by `Ric(g) + Hess f = g / (2 * λ)` with `λ > 0` and
`f` smooth, and R. Haslhofer (with R. Müller), p. 1669, eq. (1), uses `Rc + Hess f`
equal to `g / 2`. Completeness and connectedness of `M` are not part of this predicate;
they are separate hypotheses on `M`. -/
structure IsGradientRicciSoliton (f : M → ℝ) (c : ℝ) : Prop where
  /-- The potential is smooth. -/
  contMDiff : ContMDiff I 𝓘(ℝ, ℝ) ∞ f
  /-- The soliton equation `Ric + Hess f = c • g`. -/
  ricci_add_hessian : ∀ (x : M) (u v : TangentSpace I x),
    ricci I x u v + hessian I f x u v = c * inner ℝ u v

/-- A gradient shrinking Ricci soliton: a gradient Ricci soliton with `0 < c`. In
Yokota's notation (Oberwolfach Report 27/2012, p. 1651) this is `c = 1 / (2 * λ)` with
`λ > 0`; Haslhofer's normalization (p. 1669, eq. (1)) is `c = 1 / 2`. Completeness
and connectedness of `M` are not part of this predicate. -/
structure IsGradientShrinkingRicciSoliton (f : M → ℝ) (c : ℝ) : Prop
    extends IsGradientRicciSoliton I f c where
  /-- The constant is positive (shrinking). -/
  pos : 0 < c

/-- Smoothness of the Gaussian potential. -/
private theorem contMDiff_gaussian {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (a : ℝ) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ (fun x : F => (a / 2) * ‖x‖ ^ 2) := by
  rw [contMDiff_iff_contDiff]
  exact contDiff_const.mul (contDiff_norm_sq ℝ)

/-- The Hessian of the Gaussian potential `(a / 2) * ‖·‖ ^ 2` is `a • ⟪·, ·⟫`. -/
private theorem hessian_gaussian {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (a : ℝ) (x : F)
    (u v : TangentSpace 𝓘(ℝ, F) x) :
    hessian 𝓘(ℝ, F) (fun y : F => (a / 2) * ‖y‖ ^ 2) x u v =
      a * inner ℝ u v := by
  have h_sq : ContDiff ℝ ∞ (fun y : F => ‖y‖ ^ 2) := contDiff_norm_sq ℝ
  have hφ : ContDiff ℝ ∞ (fun y : F => (a / 2) * ‖y‖ ^ 2) :=
    contDiff_const.mul h_sq
  have hφ_fderiv :
      ContDiff ℝ ∞ (fderiv ℝ (fun y : F => (a / 2) * ‖y‖ ^ 2)) :=
    hφ.fderiv_right (by simp)
  have h_diff :
      DifferentiableAt ℝ (fderiv ℝ (fun y : F => (a / 2) * ‖y‖ ^ 2)) x :=
    (hφ_fderiv.differentiable (by simp)) x
  have h_hess := hessian_vectorSpace_eq_fderiv_fderiv
    (fun y : F => (a / 2) * ‖y‖ ^ 2) x u v h_diff
  have h_diff_sq : Differentiable ℝ (fun y : F => ‖y‖ ^ 2) :=
    h_sq.differentiable (by simp)
  have h_fderiv_eq : ∀ y : F,
      fderiv ℝ (fun z : F => (a / 2) * ‖z‖ ^ 2) y =
        (a / 2) • fderiv ℝ (fun z : F => ‖z‖ ^ 2) y := by
    intro y
    exact ((h_diff_sq y).hasFDerivAt.const_mul (a / 2)).fderiv
  have h_sq_fderiv : ContDiff ℝ ∞ (fderiv ℝ (fun y : F => ‖y‖ ^ 2)) :=
    h_sq.fderiv_right (by simp)
  have h_diff_sq_fderiv : ∀ y : F,
      DifferentiableAt ℝ (fderiv ℝ (fun z : F => ‖z‖ ^ 2)) y := by
    intro y
    exact ((h_sq_fderiv.differentiable (by simp)) y)
  have h_fun_eq : (fderiv ℝ (fun z : F => (a / 2) * ‖z‖ ^ 2)) =
      (fun y : F => (a / 2) • fderiv ℝ (fun z : F => ‖z‖ ^ 2) y) := by
    funext y
    exact h_fderiv_eq y
  have h_second :
      fderiv ℝ (fderiv ℝ (fun z : F => (a / 2) * ‖z‖ ^ 2)) x =
        (a / 2) • fderiv ℝ (fderiv ℝ (fun z : F => ‖z‖ ^ 2)) x := by
    rw [h_fun_eq]
    exact ((h_diff_sq_fderiv x).hasFDerivAt.const_smul (a / 2)).fderiv
  have h_inner_eq : inner ℝ u v =
      inner ℝ ((NormedSpace.fromTangentSpace x) u)
        ((NormedSpace.fromTangentSpace x) v) := rfl
  rw [h_hess, h_second]
  simp only [smul_apply, smul_eq_mul, fderiv_fderiv_norm_sq_apply, ← h_inner_eq]
  ring

/-- The Gaussian soliton on `F` with potential `(a / 2) * ‖x‖ ^ 2` and constant `a`.
For `a < 0` this is the expanding Gaussian. -/
theorem isGradientRicciSoliton_gaussian {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (a : ℝ) :
    IsGradientRicciSoliton 𝓘(ℝ, F) (fun x : F => (a / 2) * ‖x‖ ^ 2) a := by
  constructor
  · exact contMDiff_gaussian a
  · intro x u v
    have h_ricci := ricci_vectorSpace x u v
    have h_hess := hessian_gaussian a x u v
    rw [h_ricci, h_hess, zero_add]

/-- The Gaussian shrinking soliton for `0 < a`, with constant `a`. For `a = 1 / 2`
this is the Gaussian shrinker `(ℝⁿ, g_E, ‖x‖ ^ 2 / 4)` of the cited report (Yokota,
p. 1652). -/
theorem isGradientShrinkingRicciSoliton_gaussian {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (a : ℝ) (ha : 0 < a) :
    IsGradientShrinkingRicciSoliton 𝓘(ℝ, F)
      (fun x : F => (a / 2) * ‖x‖ ^ 2) a :=
  { toIsGradientRicciSoliton := isGradientRicciSoliton_gaussian a, pos := ha }

/-- For positive-dimensional `F`, the Gaussian potential is a gradient Ricci soliton
with constant `c` if and only if `a = c`. -/
theorem isGradientRicciSoliton_gaussian_iff {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [Nontrivial F] (a c : ℝ) :
    IsGradientRicciSoliton 𝓘(ℝ, F) (fun x : F => (a / 2) * ‖x‖ ^ 2) c ↔
      a = c := by
  constructor
  · intro h
    obtain ⟨u, v, huv⟩ := exists_pair_ne F
    have hw : u - v ≠ 0 := sub_ne_zero.mpr huv
    let x₀ : F := 0
    let t : TangentSpace 𝓘(ℝ, F) x₀ :=
      ((u - v : F) : TangentSpace 𝓘(ℝ, F) x₀)
    have h_eq := h.ricci_add_hessian x₀ t t
    rw [ricci_vectorSpace x₀ t t, hessian_gaussian a x₀ t t, zero_add] at h_eq
    have h_inner_pos : 0 < inner ℝ t t := by
      have h_norm : inner ℝ t t = ‖u - v‖ ^ 2 := by
        calc inner ℝ t t = inner ℝ (u - v) (u - v) := rfl
          _ = ‖u - v‖ ^ 2 := real_inner_self_eq_norm_sq (u - v)
      rw [h_norm]
      have h_pos : 0 < ‖u - v‖ := norm_pos_iff.mpr hw
      exact pow_pos h_pos 2
    have h_ne : inner ℝ t t ≠ 0 := ne_of_gt h_inner_pos
    exact mul_right_cancel₀ h_ne h_eq
  · intro h
    subst h
    exact isGradientRicciSoliton_gaussian a

/-- For positive-dimensional `F`, the Gaussian potential is a gradient shrinking Ricci
soliton with constant `c` if and only if `a = c` and `0 < c`. -/
theorem isGradientShrinkingRicciSoliton_gaussian_iff {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Nontrivial F] (a c : ℝ) :
    IsGradientShrinkingRicciSoliton 𝓘(ℝ, F)
      (fun x : F => (a / 2) * ‖x‖ ^ 2) c ↔ (a = c ∧ 0 < c) := by
  constructor
  · intro h
    have h_sol : IsGradientRicciSoliton 𝓘(ℝ, F)
        (fun x : F => (a / 2) * ‖x‖ ^ 2) c :=
      h.toIsGradientRicciSoliton
    have h_eq : a = c := (isGradientRicciSoliton_gaussian_iff a c).mp h_sol
    exact ⟨h_eq, h.pos⟩
  · rintro ⟨rfl, hc⟩
    exact isGradientShrinkingRicciSoliton_gaussian _ hc

end Manifold
