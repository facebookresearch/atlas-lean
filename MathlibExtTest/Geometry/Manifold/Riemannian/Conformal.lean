/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.Riemannian.Conformal
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Conformal scaling on Euclidean three-space

Tests for `Bundle.ContMDiffRiemannianMetric.conformalScale` and
`Manifold.conformalClass` on `EuclideanSpace ℝ (Fin 3)` with factor
`u x = 1 + ‖x‖ ^ 2`. Pins the scaled inner product, class membership,
exponential form, bad factors, constant rescaling, and dimension.
-/

@[expose] public section

open Bundle
open scoped Manifold ContDiff

noncomputable section

namespace RiemannianConformalTests

abbrev F := EuclideanSpace ℝ (Fin 3)

/-- The first basis vector, as a point of `F`. -/
def e₀ : F := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

/-- Nonconstant conformal factor. -/
def u : F → ℝ := fun x => 1 + ‖x‖ ^ 2

/-- `u` is smooth. -/
theorem hu_smooth : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ u := by
  have h_sq : ContDiff ℝ ∞ (fun x : F => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  have h_one : ContDiff ℝ ∞ (fun _ : F => (1 : ℝ)) := contDiff_const
  have h_add : ContDiff ℝ ∞ (fun x : F => 1 + ‖x‖ ^ 2) := h_one.add h_sq
  exact (contMDiff_iff_contDiff).mpr h_add

/-- `u` is positive. -/
theorem hu_pos : ∀ x : F, 0 < u x := by
  intro x
  show (0 : ℝ) < 1 + ‖x‖ ^ 2
  have h_nn : (0 : ℝ) ≤ ‖x‖ ^ 2 := sq_nonneg _
  linarith

/-- Standard metric lowered from `ω` to `∞`. -/
def g₀ : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, F) ∞ F
    (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x) :=
  (riemannianMetricVectorSpace F).ofLE le_top

/-- Conformally scaled metric with factor `u`. -/
def g₁ : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, F) ∞ F
    (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x) :=
  g₀.conformalScale u hu_smooth hu_pos

/-- Constant factor `3` is smooth. -/
theorem hu3_smooth : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ (fun _ : F => (3 : ℝ)) :=
  contMDiff_const

/-- Constant factor `3` is positive. -/
theorem hu3_pos : ∀ x : F, 0 < (fun _ : F => (3 : ℝ)) x := by
  intro x
  show (0 : ℝ) < 3
  norm_num

/-- Constant rescaling of `g₀` by `3`. -/
def g₃ : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, F) ∞ F
    (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x) :=
  g₀.conformalScale _ hu3_smooth hu3_pos

/-- Rescaling `g₁` again by `3`. -/
def g₄ : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, F) ∞ F
    (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x) :=
  g₁.conformalScale _ hu3_smooth hu3_pos

/-- Base inner product at `e₀` is `1`. -/
theorem base_inner_e₀ : inner ℝ (e₀ : F) (e₀ : F) = 1 := by
  have h1 : inner ℝ (e₀ : F) (e₀ : F)
      = (starRingEnd ℝ) (1 : ℝ)
        * (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)).ofLp 0 := by
    have h_eq : (e₀ : F) = EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := rfl
    rw [h_eq]
    exact EuclideanSpace.inner_single_left (0 : Fin 3) (1 : ℝ) _
  have h2 : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)).ofLp 0 = (1 : ℝ) := by
    simp
  have h3 : (starRingEnd ℝ) (1 : ℝ) = (1 : ℝ) := by simp
  rw [h1, h2, h3, one_mul]

/-- `e₀` is nonzero. -/
theorem e₀_ne_zero : (e₀ : F) ≠ 0 := by
  intro h0
  have h1 : inner ℝ (e₀ : F) (e₀ : F) = 1 := base_inner_e₀
  rw [h0] at h1
  simp at h1

/-- `e₀` as a tangent vector at `e₀` is nonzero. -/
theorem e₀_tangent_ne : (e₀ : TangentSpace 𝓘(ℝ, F) e₀) ≠ 0 := e₀_ne_zero

/-- `e₀` as a tangent vector at `0` is nonzero. -/
theorem e₀_at_zero_ne : (e₀ : TangentSpace 𝓘(ℝ, F) (0 : F)) ≠ 0 := e₀_ne_zero

/-- Factor value at `e₀`. -/
theorem u_at_e₀ : u e₀ = 2 := by
  have h_sq : ‖(e₀ : F)‖ ^ 2 = 1 := by
    have h1 : inner ℝ (e₀ : F) (e₀ : F) = 1 := base_inner_e₀
    have h2 : inner ℝ (e₀ : F) (e₀ : F) = ‖(e₀ : F)‖ ^ 2 :=
      real_inner_self_eq_norm_sq (e₀ : F)
    rw [h1] at h2
    exact h2.symm
  have h3 : u e₀ = 1 + ‖(e₀ : F)‖ ^ 2 := rfl
  rw [h3, h_sq]
  norm_num

/-- Factor value at the origin. -/
theorem u_at_zero : u (0 : F) = 1 := by
  have h3 : u (0 : F) = 1 + ‖(0 : F)‖ ^ 2 := rfl
  rw [h3]
  simp

/-- Standard metric value at `e₀`. -/
theorem g₀_inner_e₀ : g₀.inner e₀ e₀ e₀ = 1 := by
  have h_ofLE : g₀.inner e₀ = (riemannianMetricVectorSpace F).inner e₀ :=
    Bundle.ContMDiffRiemannianMetric.ofLE_inner _ _ _
  have h_std : (riemannianMetricVectorSpace F).inner e₀ e₀ e₀
      = inner ℝ (e₀ : F) (e₀ : F) := rfl
  rw [h_ofLE, h_std, base_inner_e₀]

/-- Scaled metric value at `e₀` is `2`. -/
theorem g₁_inner_e₀ : g₁.inner e₀ e₀ e₀ = 2 := by
  have h1 : g₁.inner e₀ e₀ e₀ = u e₀ * g₀.inner e₀ e₀ e₀ :=
    Bundle.ContMDiffRiemannianMetric.conformalScale_inner_apply
      g₀ u hu_smooth hu_pos e₀ e₀ e₀
  rw [h1, u_at_e₀, g₀_inner_e₀]
  norm_num

/-- Scaled value is nonzero. -/
theorem g₁_ne_zero : g₁.inner e₀ e₀ e₀ ≠ 0 := by
  rw [g₁_inner_e₀]
  norm_num

/-- Scaling changes the computed value. -/
theorem g₁_ne_g₀ : g₁.inner e₀ e₀ e₀ ≠ g₀.inner e₀ e₀ e₀ := by
  rw [g₁_inner_e₀, g₀_inner_e₀]
  norm_num

/-- Scaled metric lies in the conformal class. -/
theorem g₁_mem : g₁ ∈ Manifold.conformalClass g₀ :=
  Manifold.conformalScale_mem_conformalClass u hu_smooth hu_pos

/-- Symmetry of the conformal relation. -/
theorem g₀_mem_symm : g₀ ∈ Manifold.conformalClass g₁ :=
  Manifold.mem_conformalClass_symm g₁_mem

/-- Exponential form of the conformal relation. -/
theorem g₁_mem_exp : ∃ f : F → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ f ∧
    ∀ x (v w : TangentSpace 𝓘(ℝ, F) x),
      g₁.inner x v w = Real.exp (f x) * g₀.inner x v w :=
  (Manifold.mem_conformalClass_iff_exp).mp g₁_mem

/-- No metric is `0` times `g₀`. -/
theorem no_zero_factor : ¬ ∃ g' : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, F) ∞ F
    (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x), ∀ x (v w : TangentSpace 𝓘(ℝ, F) x),
      g'.inner x v w = 0 * g₀.inner x v w := by
  rintro ⟨g', hg⟩
  have h_eq : ∀ v w : TangentSpace 𝓘(ℝ, F) e₀, g'.inner e₀ v w
      = (fun _ : F => (0 : ℝ)) e₀ * g₀.inner e₀ v w := fun v w => hg e₀ v w
  have hpos := Bundle.ContMDiffRiemannianMetric.pos_of_inner_eq_mul g₀ g'
    (u := fun _ : F => (0 : ℝ)) (b := e₀) h_eq ⟨_, e₀_tangent_ne⟩
  simp at hpos

/-- No metric is `-1` times `g₀`. -/
theorem no_neg_factor : ¬ ∃ g' : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, F) ∞ F
    (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x), ∀ x (v w : TangentSpace 𝓘(ℝ, F) x),
      g'.inner x v w = (-1) * g₀.inner x v w := by
  rintro ⟨g', hg⟩
  have h_eq : ∀ v w : TangentSpace 𝓘(ℝ, F) e₀, g'.inner e₀ v w
      = (fun _ : F => (-1 : ℝ)) e₀ * g₀.inner e₀ v w := fun v w => hg e₀ v w
  have hpos := Bundle.ContMDiffRiemannianMetric.pos_of_inner_eq_mul g₀ g'
    (u := fun _ : F => (-1 : ℝ)) (b := e₀) h_eq ⟨_, e₀_tangent_ne⟩
  norm_num at hpos

/-- Constant rescaling value at `e₀`. -/
theorem g₃_inner_e₀ : g₃.inner e₀ e₀ e₀ = 3 := by
  have h1 : g₃.inner e₀ e₀ e₀
      = (fun _ : F => (3 : ℝ)) e₀ * g₀.inner e₀ e₀ e₀ :=
    Bundle.ContMDiffRiemannianMetric.conformalScale_inner_apply
      g₀ _ hu3_smooth hu3_pos e₀ e₀ e₀
  have h0 : (fun _ : F => (3 : ℝ)) e₀ = 3 := rfl
  rw [h1, h0, g₀_inner_e₀]
  norm_num

/-- Composed rescaling value: factors multiply. -/
theorem g₄_inner_e₀ : g₄.inner e₀ e₀ e₀ = 6 := by
  have h1 : g₄.inner e₀ e₀ e₀
      = (fun _ : F => (3 : ℝ)) e₀ * g₁.inner e₀ e₀ e₀ :=
    Bundle.ContMDiffRiemannianMetric.conformalScale_inner_apply
      g₁ _ hu3_smooth hu3_pos e₀ e₀ e₀
  have h0 : (fun _ : F => (3 : ℝ)) e₀ = 3 := rfl
  rw [h1, h0, g₁_inner_e₀]
  norm_num

/-- Composed rescaling stays in the class. -/
theorem g₄_mem : g₄ ∈ Manifold.conformalClass g₀ :=
  Manifold.mem_conformalClass_trans g₁_mem
    (Manifold.conformalScale_mem_conformalClass _ hu3_smooth hu3_pos)

/-- No metric has factor `‖x‖ ^ 2`, vanishing at `0`. -/
theorem no_normsq_factor : ¬ ∃ g' : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, F) ∞ F
    (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x), ∀ x (v w : TangentSpace 𝓘(ℝ, F) x),
      g'.inner x v w = ‖x‖ ^ 2 * g₀.inner x v w := by
  rintro ⟨g', hg⟩
  have h_eq : ∀ v w : TangentSpace 𝓘(ℝ, F) (0 : F), g'.inner 0 v w
      = (fun x : F => ‖x‖ ^ 2) 0 * g₀.inner 0 v w := fun v w => hg 0 v w
  have hpos := Bundle.ContMDiffRiemannianMetric.pos_of_inner_eq_mul g₀ g'
    (u := fun x : F => ‖x‖ ^ 2) (b := (0 : F)) h_eq ⟨_, e₀_at_zero_ne⟩
  have h0 : ‖(0 : F)‖ ^ 2 = 0 := by simp
  rw [h0] at hpos
  simp at hpos

/-- The dimension is `3`. -/
theorem finrank_F : Module.finrank ℝ F = 3 := finrank_euclideanSpace_fin

end RiemannianConformalTests
