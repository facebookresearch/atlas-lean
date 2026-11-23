/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.ClosedBall.Annulus
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Homotopy.Equiv

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Radius deformation inside the actual annulus

The annular radius interval deforms to `5 / 8` by an affine segment that
remains inside the interval. Products keep their first coordinate fixed.
Transport through constructed radial coordinates gives a relative
deformation of the original annulus onto its radius-`5 / 8` section.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Topology
open scoped unitInterval

universe u v w

namespace TopPair

/-- The fixed radius, strictly between the two actual overlap radii. -/
def cellAnnulusMidRadius : cellAnnulusRadii :=
  ⟨(5 : ℝ) / 8, by constructor <;> norm_num⟩

/-- Every affine radius segment stays in the actual open interval. -/
theorem cellAnnulusRadiusLine_mem (t : I) (r : cellAnnulusRadii) :
    (1 - (t : ℝ)) * (r : ℝ) + (t : ℝ) * (cellAnnulusMidRadius : ℝ) ∈
      cellAnnulusRadii := by
  change (1 - (t : ℝ)) * (r : ℝ) + (t : ℝ) * (cellAnnulusMidRadius : ℝ) ∈
    Set.Ioo ((1 : ℝ) / 2) ((3 : ℝ) / 4)
  have h := (convex_Ioo (𝕜 := ℝ) ((1 : ℝ) / 2) ((3 : ℝ) / 4)).lineMap_mem
    r.2 cellAnnulusMidRadius.2 t.2
  simpa only [AffineMap.lineMap_apply_ring] using h

/-- The actual affine interpolation of annular radii. -/
def cellAnnulusRadiusLine : C(I × cellAnnulusRadii, cellAnnulusRadii) where
  toFun p := ⟨(1 - (p.1 : ℝ)) * (p.2 : ℝ) +
      (p.1 : ℝ) * (cellAnnulusMidRadius : ℝ), by
    exact cellAnnulusRadiusLine_mem p.1 p.2⟩
  continuous_toFun := by
    exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).mul continuous_const)).subtype_mk
          (fun p => by exact cellAnnulusRadiusLine_mem p.1 p.2)

theorem cellAnnulusRadiusLine_coe (t : I) (r : cellAnnulusRadii) :
    (cellAnnulusRadiusLine (t, r) : ℝ) =
      (1 - (t : ℝ)) * (r : ℝ) + (t : ℝ) * (cellAnnulusMidRadius : ℝ) :=
  rfl

/-- The radius interval deforms to the fixed radius, fixing that radius throughout. -/
def cellAnnulusRadiusDeformation :
    ContinuousMap.HomotopyRel (ContinuousMap.id cellAnnulusRadii)
      (ContinuousMap.const cellAnnulusRadii cellAnnulusMidRadius)
      ({cellAnnulusMidRadius} : Set cellAnnulusRadii) where
  toFun := cellAnnulusRadiusLine
  continuous_toFun := by exact cellAnnulusRadiusLine.continuous
  map_zero_left r := by
    apply Subtype.ext
    change (1 - (0 : ℝ)) * (r : ℝ) + 0 * (cellAnnulusMidRadius : ℝ) = (r : ℝ)
    ring
  map_one_left r := by
    apply Subtype.ext
    change (1 - (1 : ℝ)) * (r : ℝ) + 1 * (cellAnnulusMidRadius : ℝ) =
      (cellAnnulusMidRadius : ℝ)
    ring
  prop' t r hr := by
    obtain rfl := Set.mem_singleton_iff.mp hr
    apply Subtype.ext
    change (1 - (t : ℝ)) * (cellAnnulusMidRadius : ℝ) +
      (t : ℝ) * (cellAnnulusMidRadius : ℝ) = (cellAnnulusMidRadius : ℝ)
    ring

namespace AnnulusCoordinates

variable (B : Type v) [TopologicalSpace B]

/-- The actual constant-radius section of a boundary product. -/
def productSection : C(B, B × cellAnnulusRadii) where
  toFun b := (b, cellAnnulusMidRadius)
  continuous_toFun := by exact continuous_id.prodMk continuous_const

/-- The original boundary coordinate of the product. -/
def productProjection : C(B × cellAnnulusRadii, B) where
  toFun := Prod.fst
  continuous_toFun := by exact continuous_fst

/-- The product deformation changes only the actual radius coordinate. -/
def productDeformation :
    ContinuousMap.HomotopyRel (ContinuousMap.id (B × cellAnnulusRadii))
      ((productSection B).comp (productProjection B))
      (Set.range (productSection B)) where
  toFun p := (p.2.1, cellAnnulusRadiusDeformation (p.1, p.2.2))
  continuous_toFun := by
    exact (continuous_fst.comp continuous_snd).prodMk
      (cellAnnulusRadiusDeformation.continuous.comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  map_zero_left p := by
    apply Prod.ext
    · rfl
    · change cellAnnulusRadiusDeformation (0, p.2) = p.2
      exact cellAnnulusRadiusDeformation.apply_zero p.2
  map_one_left p := by
    apply Prod.ext
    · rfl
    · change cellAnnulusRadiusDeformation (1, p.2) = cellAnnulusMidRadius
      exact cellAnnulusRadiusDeformation.apply_one p.2
  prop' t p hp := by
    obtain ⟨b, rfl⟩ := hp
    apply Prod.ext
    · rfl
    · change cellAnnulusRadiusDeformation (t, cellAnnulusMidRadius) = cellAnnulusMidRadius
      exact cellAnnulusRadiusDeformation.eq_fst t
        (Set.mem_singleton cellAnnulusMidRadius)

theorem productDeformation_fst (t : I) (p : B × cellAnnulusRadii) :
    (productDeformation B (t, p)).1 = p.1 :=
  rfl

theorem productDeformation_snd_coe (t : I) (p : B × cellAnnulusRadii) :
    ((productDeformation B (t, p)).2 : ℝ) =
      (1 - (t : ℝ)) * (p.2 : ℝ) + (t : ℝ) * (cellAnnulusMidRadius : ℝ) :=
  rfl

variable {A : Type w} [TopologicalSpace A] (h : A ≃ₜ (B × cellAnnulusRadii))

/-- The radius section transported through the constructed annular coordinates. -/
def sectionMap : C(B, A) :=
  h.symm.toHomotopyEquiv.toFun.comp (productSection B)

/-- The original boundary direction transported through the same annular coordinates. -/
def directionMap : C(A, B) :=
  (productProjection B).comp h.toHomotopyEquiv.toFun

theorem direction_section (b : B) : directionMap B h (sectionMap B h b) = b := by
  exact congrArg Prod.fst (h.apply_symm_apply (b, cellAnnulusMidRadius))

/-- Relative deformation through actual annular coordinates, fixed on the radius section. -/
def deformation :
    ContinuousMap.HomotopyRel (ContinuousMap.id A)
      ((sectionMap B h).comp (directionMap B h))
      (Set.range (sectionMap B h)) where
  toFun p := h.symm (productDeformation B (p.1, h p.2))
  continuous_toFun := by
    exact h.symm.continuous.comp ((productDeformation B).continuous.comp
      (continuous_fst.prodMk (h.continuous.comp continuous_snd)))
  map_zero_left a := by
    have hp : productDeformation B (0, h a) = h a := by
      exact (productDeformation B).apply_zero (h a)
    exact (congrArg h.symm hp).trans (h.symm_apply_apply a)
  map_one_left a := by
    exact congrArg h.symm ((productDeformation B).apply_one (h a))
  prop' t a ha := by
    obtain ⟨b, rfl⟩ := ha
    have hp : h (sectionMap B h b) = productSection B b :=
      h.apply_symm_apply (b, cellAnnulusMidRadius)
    have hf : productDeformation B (t, h (sectionMap B h b)) =
        h (sectionMap B h b) := by
      simpa only [ContinuousMap.id_apply] using
        (productDeformation B).eq_fst t ⟨b, hp.symm⟩
    exact (congrArg h.symm hf).trans (h.symm_apply_apply (sectionMap B h b))

/-- The actual boundary coordinate is fixed throughout the transported deformation. -/
theorem deformation_direction (t : I) (a : A) :
    directionMap B h (deformation B h (t, a)) = directionMap B h a := by
  change (h.toHomotopyEquiv.toFun (deformation B h (t, a))).1 =
    (h.toHomotopyEquiv.toFun a).1
  have hAtDeformation : h.toHomotopyEquiv.toFun (deformation B h (t, a)) =
      h (deformation B h (t, a)) :=
    congrFun (Homeomorph.coe_toHomotopyEquiv h) (deformation B h (t, a))
  have hRoundTrip : h (deformation B h (t, a)) =
      productDeformation B (t, h a) := by
    exact h.apply_symm_apply (productDeformation B (t, h a))
  have hAtSource : h.toHomotopyEquiv.toFun a = h a :=
    congrFun (Homeomorph.coe_toHomotopyEquiv h) a
  exact (congrArg Prod.fst hAtDeformation).trans
    ((congrArg Prod.fst hRoundTrip).trans
      ((productDeformation_fst B t (h a)).trans (congrArg Prod.fst hAtSource).symm))

/-- The actual radius changes by the specified affine interpolation. -/
theorem deformation_radius (t : I) (a : A) :
    ((h (deformation B h (t, a))).2 : ℝ) =
      (1 - (t : ℝ)) * ((h a).2 : ℝ) + (t : ℝ) * (cellAnnulusMidRadius : ℝ) := by
  exact (congrArg (fun p : B × cellAnnulusRadii => (p.2 : ℝ))
    (h.apply_symm_apply (productDeformation B (t, h a)))).trans
      (productDeformation_snd_coe B t (h a))

/-- The actual annulus and original boundary are homotopy equivalent by these coordinates. -/
def homotopyEquiv : ContinuousMap.HomotopyEquiv A B where
  toFun := directionMap B h
  invFun := sectionMap B h
  left_inv := by exact ⟨(deformation B h).toHomotopy.symm⟩
  right_inv := by
    have heq : (directionMap B h).comp (sectionMap B h) = ContinuousMap.id B := by
      apply ContinuousMap.ext
      intro b
      exact direction_section B h b
    exact ⟨(ContinuousMap.Homotopy.refl (ContinuousMap.id B)).cast heq.symm rfl⟩

end AnnulusCoordinates

variable (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The original normed annulus deforms onto its radius-five-eighths sphere section. -/
def normAnnulusDeformation :
    ContinuousMap.HomotopyRel (ContinuousMap.id (normAnnulus E))
      ((AnnulusCoordinates.sectionMap (Metric.sphere (0 : E) 1) (normAnnulusSphereProd E)).comp
        (AnnulusCoordinates.directionMap (Metric.sphere (0 : E) 1) (normAnnulusSphereProd E)))
      (Set.range
        (AnnulusCoordinates.sectionMap (Metric.sphere (0 : E) 1) (normAnnulusSphereProd E))) :=
  AnnulusCoordinates.deformation (Metric.sphere (0 : E) 1) (normAnnulusSphereProd E)

/-- Its original vector norm remains in the annulus and follows the exact radius segment. -/
theorem normAnnulusDeformation_norm (t : I) (x : normAnnulus E) :
    ‖(normAnnulusDeformation E (t, x)).1‖ =
      (1 - (t : ℝ)) * ‖x.1‖ + (t : ℝ) * (cellAnnulusMidRadius : ℝ) := by
  exact AnnulusCoordinates.deformation_radius
    (Metric.sphere (0 : E) 1) (normAnnulusSphereProd E) t x

/-- The actual lifted closed-ball annulus and its original lifted boundary
are homotopy equivalent. -/
def closedUnitBallAnnulusHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (closedUnitBallAnnulus.{u} E)
      (closedBallPair.{u} (0 : E) 1).snd :=
  AnnulusCoordinates.homotopyEquiv (closedBallPair.{u} (0 : E) 1).snd
    (closedUnitBallAnnulusSphereProd.{u} E)

end TopPair

end

end
