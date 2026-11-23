/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.ClosedBall.NDR
public import Mathlib.Analysis.Convex.Basic

import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Normalization along the full controlled closed-ball collar

The original closed-ball NDR neighborhood contains every radius strictly
greater than `1 / 2`, including radius `1`. Its original radial deformation
of `r • b`, with `b` on the original lifted unit sphere, has radius
`(1 - t) * r + t` and retains boundary direction `b` throughout.

The maps below use the original lifted ball and sphere of `closedBallPair`.
Normalization is the existing NDR retraction. In particular, it remains
constant along the original deformation from radius `5 / 8` to radius `1`.
No nonemptiness or nontriviality assumption on the normed space is needed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Topology
open scoped unitInterval

universe u v

namespace TopPair

/-- The full radius domain of the controlled unit-ball collar. -/
def cellCollarRadii : Set ℝ :=
  Set.Ioc ((1 : ℝ) / 2) 1

/-- The original unit sphere occurs at the included outer collar radius. -/
def cellCollarRadiusOne : cellCollarRadii :=
  ⟨1, by constructor <;> norm_num⟩

/-- Every controlled collar radius is strictly greater than one half. -/
theorem cellCollarRadius_half_lt (r : cellCollarRadii) :
    (1 : ℝ) / 2 < (r : ℝ) :=
  r.2.1

/-- Every controlled collar radius is positive. -/
theorem cellCollarRadius_pos (r : cellCollarRadii) :
    (0 : ℝ) < (r : ℝ) :=
  lt_trans (by norm_num : (0 : ℝ) < 1 / 2) (cellCollarRadius_half_lt r)

/-- The original unit sphere bounds the collar from above. -/
theorem cellCollarRadius_le_one (r : cellCollarRadii) :
    (r : ℝ) ≤ 1 :=
  r.2.2

/-- Controlled collar radii are nonzero. -/
theorem cellCollarRadius_ne_zero (r : cellCollarRadii) :
    (r : ℝ) ≠ 0 :=
  (cellCollarRadius_pos r).ne'

/-- The original radial NDR interpolation stays in the full collar. -/
theorem cellCollarRadiusLine_mem (t : I) (r : cellCollarRadii) :
    (1 - (t : ℝ)) * (r : ℝ) + (t : ℝ) ∈ cellCollarRadii := by
  change (1 - (t : ℝ)) * (r : ℝ) + (t : ℝ) ∈ Set.Ioc ((1 : ℝ) / 2) 1
  have h := (convex_Ioc (𝕜 := ℝ) ((1 : ℝ) / 2) 1).lineMap_mem
    r.2 cellCollarRadiusOne.2 t.2
  simpa only [AffineMap.lineMap_apply_ring, cellCollarRadiusOne, mul_one] using h

/-- The actual affine radius interpolation of the original NDR deformation. -/
def cellCollarRadiusLine : C(I × cellCollarRadii, cellCollarRadii) where
  toFun p := ⟨(1 - (p.1 : ℝ)) * (p.2 : ℝ) + (p.1 : ℝ), by
    exact cellCollarRadiusLine_mem p.1 p.2⟩
  continuous_toFun := by
    have ht : Continuous (fun p : I × cellCollarRadii => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hr : Continuous (fun p : I × cellCollarRadii => (p.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    exact (((continuous_const.sub ht).mul hr).add ht).subtype_mk _

/-- The collar interpolation uses the original scalar radius formula. -/
theorem cellCollarRadiusLine_coe (t : I) (r : cellCollarRadii) :
    (cellCollarRadiusLine (t, r) : ℝ) =
      (1 - (t : ℝ)) * (r : ℝ) + (t : ℝ) :=
  rfl

/-- At time zero, the radius is unchanged. -/
theorem cellCollarRadiusLine_zero (r : cellCollarRadii) :
    cellCollarRadiusLine (0, r) = r := by
  apply Subtype.ext
  change (1 - (0 : ℝ)) * (r : ℝ) + 0 = (r : ℝ)
  ring

/-- At time one, the radius is the original unit-sphere radius. -/
theorem cellCollarRadiusLine_one (r : cellCollarRadii) :
    cellCollarRadiusLine (1, r) = cellCollarRadiusOne := by
  apply Subtype.ext
  change (1 - (1 : ℝ)) * (r : ℝ) + 1 = 1
  ring

/-- The original boundary radius is fixed throughout the deformation. -/
theorem cellCollarRadiusLine_radiusOne (t : I) :
    cellCollarRadiusLine (t, cellCollarRadiusOne) = cellCollarRadiusOne := by
  apply Subtype.ext
  change (1 - (t : ℝ)) * 1 + (t : ℝ) = 1
  ring

section NormedGroup

variable {E : Type v} [NormedAddCommGroup E]

/-- On the entire strict half-radius collar, the existing radial scale is
the inverse of the original vector norm. -/
theorem closedUnitBallRadialScale_of_half_lt_norm
    {x : E} (hx : (1 : ℝ) / 2 < ‖x‖) :
    closedUnitBallRadialScale x = ‖x‖⁻¹ := by
  rw [closedUnitBallRadialScale, max_eq_left hx.le]

/-- The original clamped control is less than one precisely on the full
strict half-radius collar, including the original unit sphere. -/
theorem closedUnitBallControl_lt_one_iff
    (z : (closedBallPair.{u} (0 : E) 1).fst) :
    closedUnitBallControl E z < 1 ↔ (1 : ℝ) / 2 < ‖z.down.val‖ := by
  change (closedUnitBallControl E z : ℝ) < 1 ↔ (1 : ℝ) / 2 < ‖z.down.val‖
  rw [closedUnitBallControl_apply, Set.coe_projIcc, max_lt_iff, min_lt_iff]
  constructor
  · rintro ⟨_, h | h⟩
    · exact (lt_irrefl (1 : ℝ) h).elim
    · linarith
  · intro h
    refine ⟨by norm_num, Or.inr ?_⟩
    linarith

end NormedGroup

section NormedSpace

variable (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Scale the original lifted sphere vector by a full controlled collar
radius, as a point of the original lifted closed unit ball. -/
def closedUnitBallScaledBoundary :
    C((closedBallPair.{u} (0 : E) 1).snd × cellCollarRadii,
      (closedBallPair.{u} (0 : E) 1).fst) where
  toFun p := ULift.up ⟨(p.2 : ℝ) • p.1.down.val, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (cellCollarRadius_pos p.2).le,
      norm_eq_of_mem_sphere p.1.down, mul_one]
    exact cellCollarRadius_le_one p.2⟩
  continuous_toFun := by
    have hb : Continuous
        (fun p : (closedBallPair.{u} (0 : E) 1).snd × cellCollarRadii =>
          p.1.down.val) :=
      continuous_subtype_val.comp (continuous_uliftDown.comp continuous_fst)
    have hr : Continuous
        (fun p : (closedBallPair.{u} (0 : E) 1).snd × cellCollarRadii =>
          (p.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    apply continuous_uliftUp.comp
    apply Continuous.subtype_mk
    exact hr.smul hb

/-- The scaled point keeps the original lifted boundary vector. -/
theorem closedUnitBallScaledBoundary_down_val
    (b : (closedBallPair.{u} (0 : E) 1).snd) (r : cellCollarRadii) :
    (closedUnitBallScaledBoundary E (b, r)).down.val = (r : ℝ) • b.down.val :=
  rfl

/-- Its original vector norm is exactly the selected collar radius. -/
theorem closedUnitBallScaledBoundary_norm
    (b : (closedBallPair.{u} (0 : E) 1).snd) (r : cellCollarRadii) :
    ‖(closedUnitBallScaledBoundary E (b, r)).down.val‖ = (r : ℝ) := by
  rw [closedUnitBallScaledBoundary_down_val, norm_smul,
    Real.norm_of_nonneg (cellCollarRadius_pos r).le,
    norm_eq_of_mem_sphere b.down, mul_one]

/-- Radius one gives the original pair inclusion of the boundary point. -/
theorem closedUnitBallScaledBoundary_radiusOne
    (b : (closedBallPair.{u} (0 : E) 1).snd) :
    closedUnitBallScaledBoundary E (b, cellCollarRadiusOne) =
      (closedBallPair.{u} (0 : E) 1).map b := by
  apply ULift.ext
  apply Subtype.ext
  change (1 : ℝ) • b.down.val = b.down.val
  exact one_smul ℝ b.down.val

/-- The existing radial scale on the actual scaled point is the inverse radius. -/
theorem closedUnitBallRadialScale_scaledBoundary
    (b : (closedBallPair.{u} (0 : E) 1).snd) (r : cellCollarRadii) :
    closedUnitBallRadialScale (closedUnitBallScaledBoundary E (b, r)).down.val =
      (r : ℝ)⁻¹ := by
  have hhalf : (1 : ℝ) / 2 < ‖(closedUnitBallScaledBoundary E (b, r)).down.val‖ := by
    rw [closedUnitBallScaledBoundary_norm]
    exact cellCollarRadius_half_lt r
  rw [closedUnitBallRadialScale_of_half_lt_norm hhalf,
    closedUnitBallScaledBoundary_norm]

/-- The original NDR endpoint normalizes the actual scaled point to its
original boundary point, including radius one. -/
theorem closedUnitBallEndpoint_scaledBoundary
    (b : (closedBallPair.{u} (0 : E) 1).snd) (r : cellCollarRadii) :
    closedUnitBallEndpoint E (closedUnitBallScaledBoundary E (b, r)) =
      (closedBallPair.{u} (0 : E) 1).map b := by
  apply ULift.ext
  apply Subtype.ext
  change (closedUnitBallEndpoint E (closedUnitBallScaledBoundary E (b, r))).down.val =
    b.down.val
  rw [closedUnitBallEndpoint_down_val, closedUnitBallRadialScale_scaledBoundary,
    closedUnitBallScaledBoundary_down_val, smul_smul,
    inv_mul_cancel₀ (cellCollarRadius_ne_zero r), one_smul]

/-- The original control has its unclamped value on every scaled collar point. -/
theorem closedUnitBallControl_scaledBoundary_coe
    (b : (closedBallPair.{u} (0 : E) 1).snd) (r : cellCollarRadii) :
    (closedUnitBallControl E (closedUnitBallScaledBoundary E (b, r)) : ℝ) =
      2 * (1 - (r : ℝ)) := by
  have hnonneg : (0 : ℝ) ≤ 2 * (1 - (r : ℝ)) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr (cellCollarRadius_le_one r))
  have hle : 2 * (1 - (r : ℝ)) ≤ (1 : ℝ) := by
    have hhalf := cellCollarRadius_half_lt r
    linarith
  rw [closedUnitBallControl_apply, Set.coe_projIcc,
    closedUnitBallScaledBoundary_norm, min_eq_right hle, max_eq_right hnonneg]

/-- Every actual scaled collar point belongs to the original controlled neighborhood. -/
theorem closedUnitBallControl_scaledBoundary_lt_one
    (b : (closedBallPair.{u} (0 : E) 1).snd) (r : cellCollarRadii) :
    closedUnitBallControl E (closedUnitBallScaledBoundary E (b, r)) < 1 := by
  apply (closedUnitBallControl_lt_one_iff _).mpr
  rw [closedUnitBallScaledBoundary_norm]
  exact cellCollarRadius_half_lt r

/-- The same actual scaled point, now as a point of the existing NDR neighborhood. -/
def closedUnitBallControlledScaledBoundary :
    C((closedBallPair.{u} (0 : E) 1).snd × cellCollarRadii,
      (closedUnitBallNDRData.{u} E).neighborhood) where
  toFun p := ⟨closedUnitBallScaledBoundary E p, by
    change closedUnitBallControl E (closedUnitBallScaledBoundary E p) < 1
    exact closedUnitBallControl_scaledBoundary_lt_one E p.1 p.2⟩
  continuous_toFun := by
    exact (closedUnitBallScaledBoundary E).continuous.subtype_mk _

/-- The controlled point has exactly the original scaled-ball value. -/
theorem closedUnitBallControlledScaledBoundary_val
    (b : (closedBallPair.{u} (0 : E) 1).snd) (r : cellCollarRadii) :
    (closedUnitBallControlledScaledBoundary E (b, r)).1 =
      closedUnitBallScaledBoundary E (b, r) :=
  rfl

/-- The existing NDR retraction of the actual scaled point is its original
boundary point. -/
theorem closedUnitBallRetraction_controlledScaledBoundary
    (b : (closedBallPair.{u} (0 : E) 1).snd) (r : cellCollarRadii) :
    (closedUnitBallNDRData.{u} E).retraction
      (closedUnitBallControlledScaledBoundary E (b, r)) = b := by
  apply (closedBallPair.{u} (0 : E) 1).isEmbedding_map.injective
  calc
    (closedBallPair.{u} (0 : E) 1).map
        ((closedUnitBallNDRData.{u} E).retraction
          (closedUnitBallControlledScaledBoundary E (b, r))) =
        closedUnitBallEndpoint E (closedUnitBallScaledBoundary E (b, r)) :=
      (closedUnitBallNDRData.{u} E).map_retraction _
    _ = (closedBallPair.{u} (0 : E) 1).map b :=
      closedUnitBallEndpoint_scaledBoundary E b r

/-- Every original controlled-neighborhood point has a full collar radius. -/
theorem closedUnitBallCollar_norm_mem
    (z : (closedUnitBallNDRData.{u} E).neighborhood) :
    ‖z.1.down.val‖ ∈ cellCollarRadii := by
  refine ⟨?_, ?_⟩
  · have hz : closedUnitBallControl E z.1 < 1 := z.2
    exact (closedUnitBallControl_lt_one_iff z.1).mp hz
  · have hz := z.1.down.property
    change dist z.1.down.val (0 : E) ≤ 1 at hz
    simpa only [dist_zero_right] using hz

/-- The actual original vector norm as a radius of the full controlled collar. -/
def closedUnitBallCollarRadius :
    C((closedUnitBallNDRData.{u} E).neighborhood, cellCollarRadii) where
  toFun z := ⟨‖z.1.down.val‖, by exact closedUnitBallCollar_norm_mem E z⟩
  continuous_toFun := by
    have hpoint : Continuous
        (fun z : (closedUnitBallNDRData.{u} E).neighborhood => z.1.down.val) :=
      continuous_subtype_val.comp
        (continuous_uliftDown.comp continuous_subtype_val)
    exact (continuous_norm.comp hpoint).subtype_mk _

/-- The full collar radius is the norm of the original lifted vector. -/
theorem closedUnitBallCollarRadius_coe
    (z : (closedUnitBallNDRData.{u} E).neighborhood) :
    (closedUnitBallCollarRadius E z : ℝ) = ‖z.1.down.val‖ :=
  rfl

/-- The original NDR retraction normalizes every original collar vector
by its original norm. -/
theorem closedUnitBallRetraction_down_val
    (z : (closedUnitBallNDRData.{u} E).neighborhood) :
    ((closedUnitBallNDRData.{u} E).retraction z).down.val =
      ‖z.1.down.val‖⁻¹ • z.1.down.val := by
  have h := congrArg (fun w : (closedBallPair.{u} (0 : E) 1).fst => w.down.val)
    ((closedUnitBallNDRData.{u} E).map_retraction z)
  change ((closedUnitBallNDRData.{u} E).retraction z).down.val =
    (closedUnitBallEndpoint E z.1).down.val at h
  rw [closedUnitBallEndpoint_down_val,
    closedUnitBallRadialScale_of_half_lt_norm (closedUnitBallCollar_norm_mem E z).1] at h
  exact h

/-- The original retraction and original norm reconstruct the original ball point. -/
theorem closedUnitBallScaledBoundary_collarCoordinates
    (z : (closedUnitBallNDRData.{u} E).neighborhood) :
    closedUnitBallScaledBoundary E
      ((closedUnitBallNDRData.{u} E).retraction z, closedUnitBallCollarRadius E z) = z.1 := by
  have hnorm : ‖z.1.down.val‖ ≠ 0 :=
    (cellCollarRadius_pos (closedUnitBallCollarRadius E z)).ne'
  apply ULift.ext
  apply Subtype.ext
  rw [closedUnitBallScaledBoundary_down_val, closedUnitBallCollarRadius_coe,
    closedUnitBallRetraction_down_val, smul_smul, mul_inv_cancel₀ hnorm, one_smul]

/-- The same reconstruction holds inside the actual NDR neighborhood. -/
theorem closedUnitBallControlledScaledBoundary_collarCoordinates
    (z : (closedUnitBallNDRData.{u} E).neighborhood) :
    closedUnitBallControlledScaledBoundary E
      ((closedUnitBallNDRData.{u} E).retraction z, closedUnitBallCollarRadius E z) = z := by
  apply Subtype.ext
  exact closedUnitBallScaledBoundary_collarCoordinates E z

/-- The original deformation of a scaled boundary vector has the original
affine radius and exactly the same original boundary vector. -/
theorem closedUnitBallDeformationMap_scaledBoundary_down_val
    (t : I) (b : (closedBallPair.{u} (0 : E) 1).snd) (r : cellCollarRadii) :
    (closedUnitBallDeformationMap E (t, closedUnitBallScaledBoundary E (b, r))).down.val =
      ((1 - (t : ℝ)) * (r : ℝ) + (t : ℝ)) • b.down.val := by
  rw [closedUnitBallDeformationMap_down_val, closedUnitBallRadialFactor,
    closedUnitBallRadialScale_scaledBoundary, closedUnitBallScaledBoundary_down_val,
    smul_smul]
  have hmul : ((1 - (t : ℝ)) + (t : ℝ) * (r : ℝ)⁻¹) * (r : ℝ) =
      (1 - (t : ℝ)) * (r : ℝ) + (t : ℝ) := by
    rw [add_mul, mul_assoc, inv_mul_cancel₀ (cellCollarRadius_ne_zero r), mul_one]
  rw [hmul]

/-- The original NDR deformation is exactly scaling the same boundary
point by the full collar interpolation. -/
theorem closedUnitBallDeformationMap_scaledBoundary
    (t : I) (b : (closedBallPair.{u} (0 : E) 1).snd) (r : cellCollarRadii) :
    closedUnitBallDeformationMap E (t, closedUnitBallScaledBoundary E (b, r)) =
      closedUnitBallScaledBoundary E (b, cellCollarRadiusLine (t, r)) := by
  apply ULift.ext
  apply Subtype.ext
  rw [closedUnitBallDeformationMap_scaledBoundary_down_val,
    closedUnitBallScaledBoundary_down_val, cellCollarRadiusLine_coe]

/-- The original vector norm follows the affine radius throughout the original deformation. -/
theorem closedUnitBallDeformationMap_scaledBoundary_norm
    (t : I) (b : (closedBallPair.{u} (0 : E) 1).snd) (r : cellCollarRadii) :
    ‖(closedUnitBallDeformationMap E (t, closedUnitBallScaledBoundary E (b, r))).down.val‖ =
      (1 - (t : ℝ)) * (r : ℝ) + (t : ℝ) := by
  rw [closedUnitBallDeformationMap_scaledBoundary,
    closedUnitBallScaledBoundary_norm, cellCollarRadiusLine_coe]

/-- Normalizing any point of this original trajectory gives the same original boundary point. -/
theorem closedUnitBallEndpoint_deformation_scaledBoundary
    (t : I) (b : (closedBallPair.{u} (0 : E) 1).snd) (r : cellCollarRadii) :
    closedUnitBallEndpoint E
        (closedUnitBallDeformationMap E (t, closedUnitBallScaledBoundary E (b, r))) =
      (closedBallPair.{u} (0 : E) 1).map b := by
  rw [closedUnitBallDeformationMap_scaledBoundary]
  exact closedUnitBallEndpoint_scaledBoundary E b (cellCollarRadiusLine (t, r))

/-- The existing restricted NDR deformation uses the same actual scaled
points and the same full collar radius interpolation. -/
theorem closedUnitBallNeighborhoodDeformation_scaledBoundary
    (t : I) (b : (closedBallPair.{u} (0 : E) 1).snd) (r : cellCollarRadii) :
    (closedUnitBallNDRData.{u} E).neighborhoodDeformation
        (t, closedUnitBallControlledScaledBoundary E (b, r)) =
      closedUnitBallControlledScaledBoundary E (b, cellCollarRadiusLine (t, r)) := by
  apply Subtype.ext
  change closedUnitBallDeformationMap E (t, closedUnitBallScaledBoundary E (b, r)) =
    closedUnitBallScaledBoundary E (b, cellCollarRadiusLine (t, r))
  exact closedUnitBallDeformationMap_scaledBoundary E t b r

/-- On every original controlled-neighborhood point, the norm of the
original restricted deformation is `(1 - t) * ‖z‖ + t`. -/
theorem closedUnitBallNeighborhoodDeformation_norm
    (t : I) (z : (closedUnitBallNDRData.{u} E).neighborhood) :
    ‖((closedUnitBallNDRData.{u} E).neighborhoodDeformation (t, z)).1.down.val‖ =
      (1 - (t : ℝ)) * ‖z.1.down.val‖ + (t : ℝ) := by
  have h := closedUnitBallNeighborhoodDeformation_scaledBoundary E t
    ((closedUnitBallNDRData.{u} E).retraction z) (closedUnitBallCollarRadius E z)
  rw [closedUnitBallControlledScaledBoundary_collarCoordinates E z] at h
  calc
    ‖((closedUnitBallNDRData.{u} E).neighborhoodDeformation (t, z)).1.down.val‖ =
        ‖(closedUnitBallControlledScaledBoundary E
          ((closedUnitBallNDRData.{u} E).retraction z,
            cellCollarRadiusLine (t, closedUnitBallCollarRadius E z))).1.down.val‖ :=
      congrArg (fun w : (closedUnitBallNDRData.{u} E).neighborhood => ‖w.1.down.val‖) h
    _ = (cellCollarRadiusLine (t, closedUnitBallCollarRadius E z) : ℝ) :=
      closedUnitBallScaledBoundary_norm E
        ((closedUnitBallNDRData.{u} E).retraction z)
        (cellCollarRadiusLine (t, closedUnitBallCollarRadius E z))
    _ = (1 - (t : ℝ)) * (closedUnitBallCollarRadius E z : ℝ) + (t : ℝ) :=
      cellCollarRadiusLine_coe t (closedUnitBallCollarRadius E z)
    _ = (1 - (t : ℝ)) * ‖z.1.down.val‖ + (t : ℝ) := by
      rw [closedUnitBallCollarRadius_coe]

/-- The actual existing collar retraction is constant along every point
of the actual existing restricted NDR deformation. -/
theorem closedUnitBallNeighborhoodDeformation_retraction
    (t : I) (z : (closedUnitBallNDRData.{u} E).neighborhood) :
    (closedUnitBallNDRData.{u} E).retraction
        ((closedUnitBallNDRData.{u} E).neighborhoodDeformation (t, z)) =
      (closedUnitBallNDRData.{u} E).retraction z := by
  have h := closedUnitBallNeighborhoodDeformation_scaledBoundary E t
    ((closedUnitBallNDRData.{u} E).retraction z) (closedUnitBallCollarRadius E z)
  rw [closedUnitBallControlledScaledBoundary_collarCoordinates E z] at h
  exact (congrArg (fun w : (closedUnitBallNDRData.{u} E).neighborhood =>
    (closedUnitBallNDRData.{u} E).retraction w) h).trans
      (closedUnitBallRetraction_controlledScaledBoundary E
        ((closedUnitBallNDRData.{u} E).retraction z)
        (cellCollarRadiusLine (t, closedUnitBallCollarRadius E z)))

/-- The original endpoint normalization is likewise constant on the
actual existing controlled deformation. -/
theorem closedUnitBallNeighborhoodDeformation_endpoint
    (t : I) (z : (closedUnitBallNDRData.{u} E).neighborhood) :
    closedUnitBallEndpoint E
        ((closedUnitBallNDRData.{u} E).neighborhoodDeformation (t, z)).1 =
      closedUnitBallEndpoint E z.1 := by
  calc
    closedUnitBallEndpoint E
        ((closedUnitBallNDRData.{u} E).neighborhoodDeformation (t, z)).1 =
        (closedBallPair.{u} (0 : E) 1).map
          ((closedUnitBallNDRData.{u} E).retraction
            ((closedUnitBallNDRData.{u} E).neighborhoodDeformation (t, z))) :=
      ((closedUnitBallNDRData.{u} E).map_retraction _).symm
    _ = (closedBallPair.{u} (0 : E) 1).map
        ((closedUnitBallNDRData.{u} E).retraction z) :=
      congrArg (closedBallPair.{u} (0 : E) 1).map
        (closedUnitBallNeighborhoodDeformation_retraction E t z)
    _ = closedUnitBallEndpoint E z.1 :=
      (closedUnitBallNDRData.{u} E).map_retraction z

end NormedSpace

end TopPair

end

end
