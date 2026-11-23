/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.ClosedBall.Topology
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Topology.Homeomorph.Lemmas

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Radial coordinates of the actual closed-ball annulus

The strict annulus between radii `1 / 2` and `3 / 4` in the original closed
unit ball is homeomorphic to its original unit sphere times that radius
interval. The normalization is the existing normed-space radial
homeomorphism; the transport to the closed-ball pair retains the original
lifted vector and sphere points.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Topology

universe u v

namespace TopPair

/-- The actual radius interval of the cell-attachment overlap. -/
def cellAnnulusRadii : Set ℝ :=
  Set.Ioo ((1 : ℝ) / 2) ((3 : ℝ) / 4)

/-- The strict annulus in the original normed vector space. -/
def normAnnulus (E : Type v) [NormedAddCommGroup E] : Set E :=
  {x | (1 : ℝ) / 2 < ‖x‖ ∧ ‖x‖ < (3 : ℝ) / 4}

variable {E : Type v} [NormedAddCommGroup E]

theorem cellAnnulusRadii_pos (r : cellAnnulusRadii) : 0 < (r : ℝ) := by
  exact lt_trans (by norm_num : (0 : ℝ) < 1 / 2) r.2.1

theorem normAnnulus_ne_zero (x : normAnnulus E) : (x : E) ≠ 0 := by
  intro hx
  have h := x.2.1
  rw [hx, norm_zero] at h
  norm_num at h

/-- The original annular vector included in the nonzero vector space. -/
def normAnnulusNonzero (E : Type v) [NormedAddCommGroup E] :
    C(normAnnulus E, ({0}ᶜ : Set E)) where
  toFun x := ⟨x.1, by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using normAnnulus_ne_zero x⟩
  continuous_toFun := by
    exact continuous_subtype_val.subtype_mk (fun x => by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using normAnnulus_ne_zero x)

/-- The radius coordinate is exactly the original vector norm. -/
def normAnnulusRadius (E : Type v) [NormedAddCommGroup E] :
    C(normAnnulus E, cellAnnulusRadii) where
  toFun x := ⟨‖x.1‖, x.2⟩
  continuous_toFun := by
    exact (continuous_norm.comp continuous_subtype_val).subtype_mk (fun x => x.2)

theorem normAnnulusRadius_coe (x : normAnnulus E) :
    (normAnnulusRadius E x : ℝ) = ‖x.1‖ :=
  rfl

variable [NormedSpace ℝ E]

/-- The original unit-sphere coordinate supplied by the existing radial homeomorphism. -/
def normAnnulusDirection (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    C(normAnnulus E, Metric.sphere (0 : E) 1) where
  toFun x := (homeomorphUnitSphereProd E (normAnnulusNonzero E x)).1
  continuous_toFun := by
    exact continuous_fst.comp
      ((homeomorphUnitSphereProd E).continuous.comp (normAnnulusNonzero E).continuous)

/-- The original sphere point scaled by an actual annular radius remains in the annulus. -/
theorem smul_unitSphere_mem_normAnnulus (s : Metric.sphere (0 : E) 1)
    (r : cellAnnulusRadii) : (r : ℝ) • (s : E) ∈ normAnnulus E := by
  have hs : ‖(s : E)‖ = 1 :=
    norm_eq_of_mem_sphere s
  have hr : (1 : ℝ) / 2 < (r : ℝ) ∧ (r : ℝ) < (3 : ℝ) / 4 := by
    simpa only [cellAnnulusRadii, Set.mem_Ioo] using r.2
  change (1 : ℝ) / 2 < ‖(r : ℝ) • (s : E)‖ ∧
    ‖(r : ℝ) • (s : E)‖ < (3 : ℝ) / 4
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (cellAnnulusRadii_pos r), hs,
    mul_one] using hr

/-- The actual norm-space annulus, with the existing normalization and its original radius. -/
def normAnnulusSphereProd (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    normAnnulus E ≃ₜ (Metric.sphere (0 : E) 1 × cellAnnulusRadii) where
  toFun x := (normAnnulusDirection E x, normAnnulusRadius E x)
  invFun p := ⟨(p.2 : ℝ) • (p.1 : E), by
    exact smul_unitSphere_mem_normAnnulus p.1 p.2⟩
  left_inv x := by
    apply Subtype.ext
    let y := normAnnulusNonzero E x
    have hy : (y : E) = x.1 := rfl
    have hRadius : (normAnnulusRadius E x : ℝ) = ‖(y : E)‖ :=
      (normAnnulusRadius_coe x).trans (congrArg (fun z : E => ‖z‖) hy).symm
    have hDirection : (normAnnulusDirection E x : E) =
        ((homeomorphUnitSphereProd E y).1 : E) := rfl
    have hRoundTrip :
        ((homeomorphUnitSphereProd E).symm (homeomorphUnitSphereProd E y) : E) =
          (y : E) :=
      congrArg Subtype.val ((homeomorphUnitSphereProd E).symm_apply_apply y)
    have hInverse :
        ((homeomorphUnitSphereProd E).symm (homeomorphUnitSphereProd E y) : E) =
          ‖(y : E)‖ • ((homeomorphUnitSphereProd E y).1 : E) :=
      (homeomorphUnitSphereProd_symm_apply_coe E (homeomorphUnitSphereProd E y)).trans
        (congrArg (fun r : ℝ => r • ((homeomorphUnitSphereProd E y).1 : E))
          (homeomorphUnitSphereProd_apply_snd_coe E y))
    exact (congrArg₂ (fun (r : ℝ) (z : E) => r • z) hRadius hDirection).trans
      (hInverse.symm.trans (hRoundTrip.trans hy))
  right_inv p := by
    have hr : 0 < (p.2 : ℝ) := cellAnnulusRadii_pos p.2
    let r : Set.Ioi (0 : ℝ) := ⟨(p.2 : ℝ), hr⟩
    have h := (homeomorphUnitSphereProd E).apply_symm_apply (p.1, r)
    apply Prod.ext
    · apply Subtype.ext
      have hDirection := congrArg
        (fun q : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) => (q.1 : E)) h
      change ((homeomorphUnitSphereProd E)
        ((homeomorphUnitSphereProd E).symm (p.1, r))).1.val = p.1.val
      exact hDirection
    · apply Subtype.ext
      have hs : ‖(p.1 : E)‖ = 1 := norm_eq_of_mem_sphere p.1
      change ‖(p.2 : ℝ) • (p.1 : E)‖ = (p.2 : ℝ)
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hs, mul_one]
  continuous_toFun := by
    exact (normAnnulusDirection E).continuous.prodMk (normAnnulusRadius E).continuous
  continuous_invFun := by
    have hRadius : Continuous
        (fun p : Metric.sphere (0 : E) 1 × cellAnnulusRadii => (p.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    have hSphere : Continuous
        (fun p : Metric.sphere (0 : E) 1 × cellAnnulusRadii => (p.1 : E)) :=
      continuous_subtype_val.comp continuous_fst
    exact (hRadius.smul hSphere).subtype_mk
      (fun p => by exact smul_unitSphere_mem_normAnnulus p.1 p.2)

/-- The sphere coordinate is the original vector divided by its original norm. -/
theorem normAnnulusSphereProd_direction_coe (x : normAnnulus E) :
    ((normAnnulusSphereProd E x).1 : E) = ‖x.1‖⁻¹ • x.1 := by
  change ((homeomorphUnitSphereProd E (normAnnulusNonzero E x)).1 : E) =
    ‖x.1‖⁻¹ • x.1
  have hx : (normAnnulusNonzero E x : E) = x.1 := rfl
  exact (homeomorphUnitSphereProd_apply_fst_coe E (normAnnulusNonzero E x)).trans
    (congrArg (fun z : E => ‖z‖⁻¹ • z) hx)

/-- The radius coordinate retains the original vector norm. -/
theorem normAnnulusSphereProd_radius_coe (x : normAnnulus E) :
    ((normAnnulusSphereProd E x).2 : ℝ) = ‖x.1‖ :=
  rfl

/-- The inverse radial coordinates use the original radius-scaled sphere point. -/
theorem normAnnulusSphereProd_symm_coe
    (p : Metric.sphere (0 : E) 1 × cellAnnulusRadii) :
    ((normAnnulusSphereProd E).symm p : E) = (p.2 : ℝ) • (p.1 : E) :=
  rfl

/-- The actual annular subset of the original lifted closed-ball pair. -/
def closedUnitBallAnnulus (E : Type v) [NormedAddCommGroup E] :
    Set (closedBallPair.{u} (0 : E) 1).fst :=
  {z | (1 : ℝ) / 2 < ‖z.down.val‖ ∧ ‖z.down.val‖ < (3 : ℝ) / 4}

/-- Forgetting the original closed-ball and universe-lift wrappers on its actual annulus. -/
def closedUnitBallAnnulusNormHomeomorph
    (E : Type v) [NormedAddCommGroup E] :
    closedUnitBallAnnulus.{u} E ≃ₜ normAnnulus E where
  toFun z := ⟨z.1.down.val, z.2⟩
  invFun x := ⟨ULift.up ⟨x.1, by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt (lt_trans x.2.2 (by norm_num : (3 : ℝ) / 4 < 1))⟩, x.2⟩
  left_inv z := by
    apply Subtype.ext
    apply ULift.down_injective
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  continuous_toFun := by
    have hDown : Continuous (fun z : closedUnitBallAnnulus.{u} E =>
        (z.1.down : Metric.closedBall (0 : E) 1)) :=
      continuous_uliftDown.comp continuous_subtype_val
    have hValue : Continuous (fun z : closedUnitBallAnnulus.{u} E => z.1.down.val) :=
      continuous_subtype_val.comp hDown
    exact hValue.subtype_mk (fun z => z.2)
  continuous_invFun := by
    have hBall (x : normAnnulus E) : x.1 ∈ Metric.closedBall (0 : E) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt (lt_trans x.2.2 (by norm_num : (3 : ℝ) / 4 < 1))
    have hValue : Continuous (fun x : normAnnulus E =>
        (⟨x.1, hBall x⟩ : Metric.closedBall (0 : E) 1)) :=
      continuous_subtype_val.subtype_mk hBall
    have hLift : Continuous (fun x : normAnnulus E =>
        (ULift.up (⟨x.1, hBall x⟩ : Metric.closedBall (0 : E) 1) :
          (closedBallPair.{u} (0 : E) 1).fst)) :=
      continuous_uliftUp.comp hValue
    exact hLift.subtype_mk (fun x => x.2)

/-- Radial coordinates of the original lifted closed-ball annulus,
with values in its original lifted boundary sphere and the actual radius interval. -/
def closedUnitBallAnnulusSphereProd
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    closedUnitBallAnnulus.{u} E ≃ₜ (closedBallPair.{u} (0 : E) 1).snd × cellAnnulusRadii :=
  ((closedUnitBallAnnulusNormHomeomorph.{u} E).trans (normAnnulusSphereProd E)).trans
    ((Homeomorph.ulift (X := Metric.sphere (0 : E) 1)).symm.prodCongr
      (Homeomorph.refl cellAnnulusRadii))

/-- The original boundary direction is the same normalized original vector. -/
theorem closedUnitBallAnnulusSphereProd_direction (z : closedUnitBallAnnulus.{u} E) :
    (closedUnitBallAnnulusSphereProd.{u} E z).1.down.val =
      ‖z.1.down.val‖⁻¹ • z.1.down.val := by
  exact normAnnulusSphereProd_direction_coe (closedUnitBallAnnulusNormHomeomorph.{u} E z)

/-- The annular radius remains the norm of the same original lifted vector. -/
theorem closedUnitBallAnnulusSphereProd_radius (z : closedUnitBallAnnulus.{u} E) :
    ((closedUnitBallAnnulusSphereProd.{u} E z).2 : ℝ) = ‖z.1.down.val‖ :=
  rfl

/-- The inverse coordinates retain the original boundary lift and scale its original vector. -/
theorem closedUnitBallAnnulusSphereProd_symm_val
    (p : (closedBallPair.{u} (0 : E) 1).snd × cellAnnulusRadii) :
    ((closedUnitBallAnnulusSphereProd.{u} E).symm p).1.down.val =
      (p.2 : ℝ) • p.1.down.val :=
  rfl

end TopPair

end

end
