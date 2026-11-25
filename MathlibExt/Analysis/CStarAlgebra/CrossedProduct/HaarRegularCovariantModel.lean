/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.PointwiseOperator
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarRegularRepresentation
public import MathlibExt.Analysis.CStarAlgebra.PointNormAction
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The original regular covariant model from an actual coefficient representation

On the original Lp H 2 Haar carrier, the coefficient at s is
rho(alpha(s inverse)(a)) applied to the original vector at s. The computed
bounded pointwise operator gives this literal formula on all L2 vectors.
The existing Haar left unitaries and these coefficient operators satisfy
the original covariance identity and define the actual regular pair.

The input is the original coefficient star representation, with independent
group, coefficient and Hilbert universes. No regular model, desired output
identity, countability or raw-core faithfulness is assumed. A canonical
source construction may later select an existing faithful GN representation;
source model independence remains a separate obligation.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped CStarAlgebra InnerProductSpace

namespace PointNormCStarAction

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : PointNormCStarAction G A) (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- The original inverse-action coefficient field on the original Hilbert vectors. -/
def regularCoefficientField (a : A) : G → H →L[ℂ] H := fun s => ρ (α s⁻¹ a)

/-- The original point-norm action makes its coefficient field jointly vector continuous. -/
theorem continuous_regularCoefficientField_action (a : A) :
    Continuous (fun z : G × H => regularCoefficientField α ρ a z.1 z.2) := by
  have hρ : Continuous (ρ : A → (H →L[ℂ] H)) := map_continuous ρ
  exact ((hρ.comp ((α.continuous_orbit a).comp continuous_inv)).comp
    continuous_fst).clm_apply continuous_snd

omit [IsTopologicalGroup G] in
/-- The original coefficient norm uniformly bounds this actual operator field. -/
theorem norm_regularCoefficientField_le (a : A) (s : G) :
    ‖regularCoefficientField α ρ a s‖ ≤ ‖a‖ := by
  change ‖ρ (α s⁻¹ a)‖ ≤ ‖a‖
  exact (NonUnitalStarAlgHom.norm_apply_le ρ (α s⁻¹ a)).trans (α.norm_apply s⁻¹ a).le

variable [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.Regular]

/-- The actual original regular coefficient operator on the same vector-valued L2 carrier. -/
def regularCoefficientOperator (a : A) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  HaarL2.pointwiseOperator (regularCoefficientField α ρ a)
    (continuous_regularCoefficientField_action α ρ a) μ ‖a‖
    (norm_regularCoefficientField_le α ρ a)

/-- Every original L2 vector retains the printed inverse-action coefficient formula. -/
theorem regularCoefficientOperator_ae_eq (a : A) (ξ : Lp H 2 μ) :
    regularCoefficientOperator α ρ μ a ξ =ᵐ[μ] fun s : G => ρ (α s⁻¹ a) (ξ s) :=
  HaarL2.pointwiseOperator_ae_eq (regularCoefficientField α ρ a)
    (continuous_regularCoefficientField_action α ρ a) μ ‖a‖
    (norm_regularCoefficientField_le α ρ a) ξ

/-- The original coefficient norm bounds every actual L2 image. -/
theorem norm_regularCoefficientOperator_apply_le (a : A) (ξ : Lp H 2 μ) :
    ‖regularCoefficientOperator α ρ μ a ξ‖ ≤ ‖a‖ * ‖ξ‖ :=
  HaarL2.pointwiseOperator_norm_apply_le (regularCoefficientField α ρ a)
    (continuous_regularCoefficientField_action α ρ a) μ ‖a‖
    (norm_regularCoefficientField_le α ρ a) ξ

/-- The actual regular coefficient operators preserve original coefficient addition. -/
theorem regularCoefficientOperator_add (a b : A) :
    regularCoefficientOperator α ρ μ (a + b) =
      regularCoefficientOperator α ρ μ a + regularCoefficientOperator α ρ μ b := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [regularCoefficientOperator_ae_eq α ρ μ (a + b) ξ,
    regularCoefficientOperator_ae_eq α ρ μ a ξ,
    regularCoefficientOperator_ae_eq α ρ μ b ξ,
    Lp.coeFn_add (regularCoefficientOperator α ρ μ a ξ) (regularCoefficientOperator α ρ μ b ξ)]
    with s h₁ h₂ h₃ h₄
  change regularCoefficientOperator α ρ μ (a + b) ξ s =
    (regularCoefficientOperator α ρ μ a ξ + regularCoefficientOperator α ρ μ b ξ) s
  rw [h₁, h₄, Pi.add_apply, h₂, h₃, map_add (α.aut s⁻¹), map_add ρ]
  rfl

/-- The actual regular coefficient operators preserve original complex scaling. -/
theorem regularCoefficientOperator_smul (c : ℂ) (a : A) :
    regularCoefficientOperator α ρ μ (c • a) = c • regularCoefficientOperator α ρ μ a := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [regularCoefficientOperator_ae_eq α ρ μ (c • a) ξ,
    regularCoefficientOperator_ae_eq α ρ μ a ξ,
    Lp.coeFn_smul c (regularCoefficientOperator α ρ μ a ξ)] with s h₁ h₂ h₃
  change regularCoefficientOperator α ρ μ (c • a) ξ s =
    (c • regularCoefficientOperator α ρ μ a ξ) s
  rw [h₁, h₃, Pi.smul_apply, h₂, map_smul (α.aut s⁻¹), map_smul ρ]
  rfl

/-- The actual regular coefficient operators preserve original coefficient multiplication. -/
theorem regularCoefficientOperator_mul (a b : A) :
    regularCoefficientOperator α ρ μ (a * b) =
      regularCoefficientOperator α ρ μ a * regularCoefficientOperator α ρ μ b := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [regularCoefficientOperator_ae_eq α ρ μ (a * b) ξ,
    regularCoefficientOperator_ae_eq α ρ μ a (regularCoefficientOperator α ρ μ b ξ),
    regularCoefficientOperator_ae_eq α ρ μ b ξ] with s h₁ h₂ h₃
  change regularCoefficientOperator α ρ μ (a * b) ξ s =
    regularCoefficientOperator α ρ μ a (regularCoefficientOperator α ρ μ b ξ) s
  rw [h₁, h₂, h₃, map_mul (α.aut s⁻¹), map_mul ρ]
  rfl

/-- The original coefficient involution gives the actual L2 operator adjoint. -/
theorem regularCoefficientOperator_star (a : A) :
    regularCoefficientOperator α ρ μ (star a) = star (regularCoefficientOperator α ρ μ a) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff
    (regularCoefficientOperator α ρ μ (star a)) (regularCoefficientOperator α ρ μ a)).mpr
  intro ξ η
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularCoefficientOperator_ae_eq α ρ μ (star a) ξ,
    regularCoefficientOperator_ae_eq α ρ μ a η] with s h₁ h₂
  rw [h₁, h₂, StarHomClass.map_star (α.aut s⁻¹), StarHomClass.map_star ρ]
  change ⟪star (ρ (α s⁻¹ a)) (ξ s), η s⟫_ℂ = ⟪ξ s, ρ (α s⁻¹ a) (η s)⟫_ℂ
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left (ρ (α s⁻¹ a)) (η s) (ξ s)

/-- The computed original regular coefficient representation is a nonunital complex star hom. -/
def regularCoefficientHom : A →⋆ₙₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ) where
  toFun := regularCoefficientOperator α ρ μ
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro ξ
    apply Lp.ext
    filter_upwards [regularCoefficientOperator_ae_eq α ρ μ (0 : A) ξ,
      Lp.coeFn_zero H 2 μ] with s h₁ h₂
    change regularCoefficientOperator α ρ μ (0 : A) ξ s = (0 : Lp H 2 μ) s
    rw [h₁, h₂, map_zero (α.aut s⁻¹), map_zero ρ]
    rfl
  map_add' := regularCoefficientOperator_add α ρ μ
  map_mul' := regularCoefficientOperator_mul α ρ μ
  map_smul' := regularCoefficientOperator_smul α ρ μ
  map_star' := regularCoefficientOperator_star α ρ μ

variable [μ.IsHaarMeasure]

/-- The original Haar left translations and coefficient operators satisfy original covariance. -/
theorem regularCoefficientOperator_covariance (g : G) (a : A) :
    (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
        Lp H 2 μ →L[ℂ] Lp H 2 μ) * regularCoefficientOperator α ρ μ a *
      star (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
        Lp H 2 μ →L[ℂ] Lp H 2 μ) = regularCoefficientOperator α ρ μ (α g a) := by
  rw [StronglyContinuousUnitaryRepresentation.star_haarLeftRegular]
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  let L (h : G) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
    StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H h
  let η := L g⁻¹ ξ
  have houter := StronglyContinuousUnitaryRepresentation.haarLeftRegular_ae_eq G μ H g
    (regularCoefficientOperator α ρ μ a η)
  have hcoefficient := regularCoefficientOperator_ae_eq α ρ μ a η
  have hinner := StronglyContinuousUnitaryRepresentation.haarLeftRegular_ae_eq G μ H g⁻¹ ξ
  have hpres : MeasurePreserving (fun s : G => g⁻¹ * s) μ μ := measurePreserving_smul g⁻¹ μ
  have hquasi : QuasiMeasurePreserving (fun s : G => g⁻¹ * s) μ μ :=
    ⟨hpres.measurable.aemeasurable, by rw [hpres.map_eq]⟩
  have hcoefficient' := hquasi.ae_eq_comp hcoefficient
  have hinner' := hquasi.ae_eq_comp hinner
  filter_upwards [houter, hcoefficient', hinner', regularCoefficientOperator_ae_eq α ρ μ (α g a) ξ]
    with s h₁ h₂ h₃ h₄
  change L g (regularCoefficientOperator α ρ μ a (L g⁻¹ ξ)) s =
    regularCoefficientOperator α ρ μ (α g a) ξ s
  simp only [Function.comp_apply] at h₂ h₃
  rw [h₁, h₂, h₃, h₄]
  simp only [mul_inv_rev, inv_inv, mul_inv_cancel_left]
  exact congrArg (fun b : A => ρ b (ξ s)) (α.apply_mul s⁻¹ g a)

/-- The actual original regular covariant pair on the original vector-valued Haar L2 carrier. -/
def regularCovariantRepresentation : CovariantRepresentation α (Lp H 2 μ) where
  algebra := regularCoefficientHom α ρ μ
  group := StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H
  covariance := by
    intro g a
    change (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
        Lp H 2 μ →L[ℂ] Lp H 2 μ) * regularCoefficientOperator α ρ μ a *
      star (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
        Lp H 2 μ →L[ℂ] Lp H 2 μ) = regularCoefficientOperator α ρ μ (α g a)
    exact regularCoefficientOperator_covariance α ρ μ g a

end

end PointNormCStarAction
