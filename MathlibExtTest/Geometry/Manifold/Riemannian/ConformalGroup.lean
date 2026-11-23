/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Manifold.Riemannian.ConformalGroup
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Conformal group versus isometry group on Euclidean 3-space

Tests dilation, negation, invariant class and the conformal bridge.
-/

@[expose] public section

open Manifold
open scoped Manifold ContDiff Bundle

noncomputable section

namespace ConformalGroupTests

abbrev F := EuclideanSpace ℝ (Fin 3)

/-- Standard basis vector. -/
def e₀ : F := EuclideanSpace.single 0 1

/-- Standard metric lowered to `∞`. -/
def g₀ : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, F) ∞ F
    (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x) :=
  (riemannianMetricVectorSpace F).ofLE le_top

/-- Scaling linear equivalence. -/
def eCL : F ≃L[ℝ] F :=
  LinearEquiv.toContinuousLinearEquiv
    (LinearEquiv.smulOfNeZero ℝ F 2 (by norm_num))

/-- Dilation diffeomorphism. -/
def δ : F ≃ₘ^∞⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ F := eCL.toDiffeomorph

/-- Negation linear equivalence. -/
def νCL : F ≃L[ℝ] F := ContinuousLinearEquiv.neg ℝ

/-- Negation diffeomorphism. -/
def ν : F ≃ₘ^∞⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ F := νCL.toDiffeomorph

/-- Conformal factor. -/
def u : F → ℝ := fun x => 1 + ‖x - e₀‖ ^ 2

/-- Smoothness of the factor. -/
theorem hu_smooth : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ u := by
  have hsub : ContDiff ℝ ∞ (fun x : F => x - e₀) :=
    contDiff_id.sub contDiff_const
  have hnorm : ContDiff ℝ ∞ (fun x : F => ‖x‖ ^ 2) :=
    contDiff_norm_sq ℝ
  have hcomp : ContDiff ℝ ∞ (fun x : F => ‖x - e₀‖ ^ 2) :=
    hnorm.comp hsub
  have hfull : ContDiff ℝ ∞ u := by
    show ContDiff ℝ ∞ (fun x : F => 1 + ‖x - e₀‖ ^ 2)
    exact contDiff_const.add hcomp
  exact contMDiff_iff_contDiff.mpr hfull

/-- Positivity of the factor. -/
theorem hu_pos (x : F) : 0 < u x := by
  have hnn : (0 : ℝ) ≤ ‖x - e₀‖ ^ 2 := sq_nonneg _
  show 0 < 1 + ‖x - e₀‖ ^ 2
  linarith

/-- Scaled metric. -/
def g₂ : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, F) ∞ F
    (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x) :=
  g₀.conformalScale u hu_smooth hu_pos

/-- Norm of `e₀` is one. -/
theorem norm_e₀ : ‖e₀‖ = 1 := by
  have h : ‖e₀‖ = ‖(1 : ℝ)‖ :=
    PiLp.norm_single 2 (fun _ : Fin 3 => ℝ) 0 1
  rw [h]
  simp

/-- Inner product of `e₀` with itself. -/
theorem inner_e₀ : inner ℝ (e₀ : F) (e₀ : F) = 1 := by
  have h : inner ℝ (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) = 1 := by
    rw [EuclideanSpace.inner_single_left]
    simp
  exact h

/-- Differential of dilation is scaling. -/
theorem hδ_deriv (x : F) (v : TangentSpace 𝓘(ℝ, F) x) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) ⇑δ x v = (2 : ℝ) • v := by
  have hcoe : (⇑δ : F → F) = ⇑eCL :=
    ContinuousLinearEquiv.coe_toDiffeomorph eCL
  rw [hcoe, mfderiv_eq_fderiv, ContinuousLinearEquiv.fderiv]
  rfl

/-- Differential of negation is negation. -/
theorem hν_deriv (x : F) (v : TangentSpace 𝓘(ℝ, F) x) :
    mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) ⇑ν x v = -v := by
  have hcoe : (⇑ν : F → F) = ⇑νCL :=
    ContinuousLinearEquiv.coe_toDiffeomorph νCL
  rw [hcoe, mfderiv_eq_fderiv, ContinuousLinearEquiv.fderiv]
  rfl

/-- Dilation is conformal with factor four. -/
theorem δ_isConformal : IsConformalDiffeomorph g₀ g₀ δ := by
  let : Bundle.RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x) :=
    ⟨g₀.toRiemannianMetric⟩
  refine ⟨fun _ => 4, contMDiff_const, fun _ => by norm_num, ?_⟩
  intro x v w
  have hdv : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) ⇑δ x v = (2 : ℝ) • v :=
    hδ_deriv x v
  have hdw : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) ⇑δ x w = (2 : ℝ) • w :=
    hδ_deriv x w
  have e1 : g₀.inner (δ x) ((2 : ℝ) • v) ((2 : ℝ) • w) =
      inner ℝ ((2 : ℝ) • v) ((2 : ℝ) • w) := rfl
  have e2 : g₀.inner x v w = inner ℝ v w := rfl
  rw [hdv, hdw, e1, e2, inner_smul_left, inner_smul_right]
  simp
  ring

/-- Dilation lies in the conformal group. -/
theorem δ_mem_conformal : δ ∈ conformalGroup g₀ :=
  (mem_conformalGroup g₀ δ).mpr δ_isConformal

/-- Base value of the metric. -/
theorem pin_g0 : g₀.inner (0 : F) e₀ e₀ = 1 := by
  have e1 : g₀.inner (0 : F) e₀ e₀ = inner ℝ (e₀ : F) (e₀ : F) := rfl
  rw [e1, inner_e₀]

/-- Pulled-back value is four. -/
theorem pin_pullback : g₀.inner (δ 0)
    (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) ⇑δ 0 e₀)
    (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) ⇑δ 0 e₀) = 4 := by
  have hder : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) ⇑δ (0 : F) e₀ =
      (2 : ℝ) • e₀ := hδ_deriv 0 e₀
  have e1 : g₀.inner (δ 0) ((2 : ℝ) • e₀) ((2 : ℝ) • e₀) =
      inner ℝ ((2 : ℝ) • (e₀ : F)) ((2 : ℝ) • (e₀ : F)) := rfl
  rw [hder, e1, inner_smul_left, inner_smul_right, inner_e₀]
  simp
  ring

/-- Dilation is not an isometry. -/
theorem δ_not_isometry : δ ∉ isometryGroup g₀ := by
  intro hmem
  have h := (mem_isometryGroup g₀ δ).mp hmem 0 e₀ e₀
  rw [pin_pullback, pin_g0] at h
  have h41 : (4 : ℝ) ≠ 1 := by norm_num
  exact h41 h

/-- Negation is an isometry. -/
theorem ν_isometry : IsIsometryDiffeomorph g₀ g₀ ν := by
  let : Bundle.RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x) :=
    ⟨g₀.toRiemannianMetric⟩
  intro x v w
  have hdv : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) ⇑ν x v = -v := hν_deriv x v
  have hdw : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) ⇑ν x w = -w := hν_deriv x w
  have e1 : g₀.inner (ν x) (-v) (-w) = inner ℝ (-v) (-w) := rfl
  have e2 : g₀.inner x v w = inner ℝ v w := rfl
  rw [hdv, hdw, e1, e2]
  simp

/-- Negation lies in the isometry group. -/
theorem ν_mem_isometry : ν ∈ isometryGroup g₀ :=
  (mem_isometryGroup g₀ ν).mpr ν_isometry

/-- Isometries are conformal. -/
theorem groups_le : isometryGroup g₀ ≤ conformalGroup g₀ :=
  isometryGroup_le_conformalGroup g₀

/-- The two groups differ. -/
theorem groups_ne : isometryGroup g₀ ≠ conformalGroup g₀ := by
  intro h
  have hc : δ ∈ conformalGroup g₀ := δ_mem_conformal
  rw [← h] at hc
  exact δ_not_isometry hc

/-- The metric is invariant under isometries. -/
theorem self_invariant :
    g₀ ∈ invariantConformalClass g₀ ↑(isometryGroup g₀) :=
  self_mem_invariantConformalClass g₀ _
    (fun σ hσ => (mem_isometryGroup g₀ σ).mp hσ)

/-- Value of `u` at `e₀`. -/
theorem pin_u_e₀ : u e₀ = 1 := by
  have hsub : e₀ - e₀ = (0 : F) := sub_self e₀
  have h0 : ‖(0 : F)‖ ^ 2 = (0 : ℝ) := by simp
  show 1 + ‖e₀ - e₀‖ ^ 2 = 1
  rw [hsub, h0, add_zero]

/-- Value of `u` at `-e₀`. -/
theorem pin_u_neg : u (-e₀) = 5 := by
  have hsub : (-e₀ : F) - e₀ = -((2 : ℝ) • e₀) := by
    rw [two_smul, neg_add, sub_eq_add_neg]
  have hnorm : ‖(-e₀ : F) - e₀‖ = 2 := by
    rw [hsub, norm_neg, norm_smul, norm_e₀, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  show 1 + ‖(-e₀) - e₀‖ ^ 2 = 5
  rw [hnorm]
  norm_num

/-- Base value at the antipode. -/
theorem pin_g0_neg : g₀.inner (-e₀) (-e₀) (-e₀) = 1 := by
  have e1 : g₀.inner (-e₀) (-e₀) (-e₀) =
      inner ℝ (-(e₀ : F)) (-(e₀ : F)) := rfl
  rw [e1, inner_neg_left, inner_neg_right, neg_neg, inner_e₀]

/-- Base value at `e₀` as tangent vectors. -/
theorem pin_g0_e₀ : g₀.inner e₀ e₀ e₀ = 1 := by
  have e1 : g₀.inner e₀ e₀ e₀ = inner ℝ (e₀ : F) (e₀ : F) := rfl
  rw [e1, inner_e₀]

/-- Scaled metric lies in the class. -/
theorem g₂_mem_class : g₂ ∈ conformalClass g₀ :=
  conformalScale_mem_conformalClass u hu_smooth hu_pos

/-- Scaled metric is not `ν`-invariant. -/
theorem g₂_not_invariant :
    g₂ ∉ invariantConformalClass g₀ {ν} := by
  intro hmem
  obtain ⟨_, hinv⟩ := hmem
  have hνmem : ν ∈ ({ν} : Set _) := by simp
  have hiso := hinv ν hνmem e₀ e₀ e₀
  have hνe : ν e₀ = -e₀ := by
    have hcoe : (⇑ν : F → F) = ⇑νCL :=
      ContinuousLinearEquiv.coe_toDiffeomorph νCL
    rw [hcoe]
    rfl
  have hder : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) ⇑ν e₀ e₀ = -e₀ :=
    hν_deriv e₀ e₀
  rw [hder, hνe] at hiso
  have hscale : ∀ (y : F) (a b : F),
      g₂.inner y a b = u y * g₀.inner y a b := fun y a b =>
    Bundle.ContMDiffRiemannianMetric.conformalScale_inner_apply
      g₀ u hu_smooth hu_pos y a b
  rw [hscale, hscale, pin_u_neg, pin_u_e₀, pin_g0_neg, pin_g0_e₀] at hiso
  norm_num at hiso

/-- Bridge to conformal linear maps. -/
theorem bridge :
    letI : Bundle.RiemannianBundle
      (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x) :=
      ⟨g₀.toRiemannianMetric⟩;
    IsConformalMap (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) ⇑δ 0) :=
  isConformalMap_mfderiv_of_mem_conformalGroup δ_mem_conformal 0

/-- Product stays conformal. -/
theorem mul_mem_conformal : δ * δ ∈ conformalGroup g₀ :=
  mul_mem δ_mem_conformal δ_mem_conformal

/-- Inverse stays conformal. -/
theorem inv_mem_conformal : δ⁻¹ ∈ conformalGroup g₀ :=
  inv_mem δ_mem_conformal

/-- Dilation acts by four on `e₀`. -/
theorem pin_mul_e₀ : (δ * δ) e₀ = (4 : ℝ) • e₀ := by
  have h1 : (δ * δ) e₀ = δ (δ e₀) := rfl
  have hδ : ∀ x : F, δ x = (2 : ℝ) • x := by
    intro x
    have hcoe : (⇑δ : F → F) = ⇑eCL :=
      ContinuousLinearEquiv.coe_toDiffeomorph eCL
    rw [hcoe]
    rfl
  rw [h1, hδ, hδ, smul_smul]
  have h44 : (2 : ℝ) * 2 = 4 := by norm_num
  rw [h44]

end ConformalGroupTests

end
