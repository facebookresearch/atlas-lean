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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.Basic
public import MathlibExt.MeasureTheory.Group.ModularCharacterContinuity

/-!
# The original Haar twisted involution

The coefficient at `s` is the positive-real modular weight times the action at `s`
of the adjoint coefficient at `s⁻¹`. The positive-real weight is written through
its canonical complex scalar image, using exactly the original complex module.
Only the additive, involutive and conjugate-linear structures are installed here;
the convolution multiplication has a separate owner.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set MeasureTheory
open scoped CompactlySupported NNReal Pointwise CStarAlgebra

namespace HaarTwistedCore

noncomputable section

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]

/-- The literal modularly weighted adjoint coefficient function, with its original
compact support and continuous action. -/
def crossedStarCc (α : PointNormCStarAction G A) (f : C_c(G, A)) : C_c(G, A) where
  toFun s := ((Measure.modularCharacter s : ℝ) : ℂ) • α s (star (f s⁻¹))
  continuous_toFun := by
    have hδ : Continuous (fun s : G => ((Measure.modularCharacter s : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        (continuous_subtype_val.comp Measure.continuous_modularCharacter)
    exact hδ.smul (α.continuous_apply continuous_id ((map_continuous f).comp continuous_inv).star)
  hasCompactSupport' := by
    refine HasCompactSupport.intro f.hasCompactSupport.inv ?_
    intro s hs
    have hzero : f s⁻¹ = 0 := by
      by_contra hne
      apply hs
      change s⁻¹ ∈ tsupport (f : G → A)
      exact subset_closure hne
    simp only [hzero, star_zero, PointNormCStarAction.apply_zero, smul_zero]

omit [MeasurableSpace G] in
/-- Evaluation of the original compact-support involution retains its Haar modular factor. -/
@[simp]
theorem crossedStarCc_apply (α : PointNormCStarAction G A) (f : C_c(G, A)) (s : G) :
    crossedStarCc α f s = ((Measure.modularCharacter s : ℝ) : ℂ) • α s (star (f s⁻¹)) :=
  rfl

omit [MeasurableSpace G] in
/-- Involuting a coefficient can only invert its original topological support. -/
theorem tsupport_crossedStarCc_subset (α : PointNormCStarAction G A) (f : C_c(G, A)) :
    tsupport (crossedStarCc α f : G → A) ⊆ (tsupport (f : G → A))⁻¹ := by
  refine closure_minimal ?_ (isClosed_tsupport (f : G → A)).inv
  intro s hs
  have hne : f s⁻¹ ≠ 0 := by
    intro hzero
    apply hs
    simp only [crossedStarCc_apply, hzero, star_zero, PointNormCStarAction.apply_zero, smul_zero]
  change s⁻¹ ∈ tsupport (f : G → A)
  exact subset_closure hne

variable (μ : Measure G) (α : PointNormCStarAction G A)

/-- The Haar twisted involution on the same measure- and action-indexed coefficient carrier. -/
def crossedStar (f : Carrier μ α) : Carrier μ α :=
  fromCc μ α (crossedStarCc α (toCc μ α f))

/-- The indexed involution has the exact original modularly weighted coefficient value. -/
@[simp]
theorem crossedStar_apply (f : Carrier μ α) (s : G) :
    crossedStar μ α f s = ((Measure.modularCharacter s : ℝ) : ℂ) • α s (star (f s⁻¹)) :=
  rfl

/-- The original twisted involution preserves addition of coefficient functions. -/
theorem crossedStar_add (f g : Carrier μ α) :
    crossedStar μ α (f + g) = crossedStar μ α f + crossedStar μ α g := by
  apply (equivCc μ α).injective
  change toCc μ α (crossedStar μ α (f + g)) =
    toCc μ α (crossedStar μ α f + crossedStar μ α g)
  rw [toCc_add]
  apply CompactlySupportedContinuousMap.ext
  intro s
  simp only [crossedStar, toCc_fromCc, crossedStarCc_apply, toCc_add,
    CompactlySupportedContinuousMap.add_apply, star_add, PointNormCStarAction.apply_add, smul_add]

/-- The original twisted involution is conjugate-linear for the original complex module. -/
theorem crossedStar_smul (c : ℂ) (f : Carrier μ α) :
    crossedStar μ α (c • f) = star c • crossedStar μ α f := by
  apply (equivCc μ α).injective
  change toCc μ α (crossedStar μ α (c • f)) = toCc μ α (star c • crossedStar μ α f)
  rw [toCc_smul]
  apply CompactlySupportedContinuousMap.ext
  intro s
  simp only [crossedStar, toCc_fromCc, crossedStarCc_apply, toCc_smul,
    CompactlySupportedContinuousMap.smul_apply, star_smul, PointNormCStarAction.apply_smul]
  exact smul_comm _ _ _

/-- Applying the source involution twice restores the original coefficient function. -/
theorem crossedStar_crossedStar (f : Carrier μ α) :
    crossedStar μ α (crossedStar μ α f) = f := by
  apply (equivCc μ α).injective
  change toCc μ α (crossedStar μ α (crossedStar μ α f)) = toCc μ α f
  apply CompactlySupportedContinuousMap.ext
  intro s
  have hδ : ((Measure.modularCharacter s : ℝ) : ℂ) *
      ((Measure.modularCharacter s⁻¹ : ℝ) : ℂ) = 1 := by
    have h : Measure.modularCharacter s * Measure.modularCharacter s⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hreal : (Measure.modularCharacter s : ℝ) *
        (Measure.modularCharacter s⁻¹ : ℝ) = 1 := by exact_mod_cast h
    exact_mod_cast hreal
  have hstarδ : star ((Measure.modularCharacter s⁻¹ : ℝ) : ℂ) =
      ((Measure.modularCharacter s⁻¹ : ℝ) : ℂ) := by simp
  simp only [crossedStar, toCc_fromCc, crossedStarCc_apply, inv_inv]
  change ((Measure.modularCharacter s : ℝ) : ℂ) •
    α s (star (((Measure.modularCharacter s⁻¹ : ℝ) : ℂ) • α s⁻¹ (star (f s)))) = f s
  rw [star_smul, hstarδ, ← PointNormCStarAction.apply_star, star_star,
    PointNormCStarAction.apply_smul, PointNormCStarAction.apply_apply_inv, ← mul_smul, hδ, one_smul]

/-- The core's star is the original Haar twisted involution. -/
instance instStarCarrier : Star (Carrier μ α) :=
  ⟨crossedStar μ α⟩

/-- The original modular character and inverse action make the core's star involutive. -/
instance instInvolutiveStarCarrier : InvolutiveStar (Carrier μ α) where
  star_involutive := crossedStar_crossedStar μ α

/-- The original additive coefficient group has its source twisted star structure. -/
instance instStarAddMonoidCarrier : StarAddMonoid (Carrier μ α) where
  star_add := crossedStar_add μ α

/-- The original complex module has its source conjugate-linear twisted star structure. -/
instance instStarModuleCarrier : StarModule ℂ (Carrier μ α) where
  star_smul := crossedStar_smul μ α

end

end HaarTwistedCore
