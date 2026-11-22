/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.ClosedBall.Topology
public import MathlibExt.Topology.Category.TopPair.NDRCofibration
import Mathlib.Topology.Order.ProjIcc

/-!
# NDR data for closed unit balls

The sphere in a closed unit ball has controlled NDR data.  On radii at least `1 / 2`, the
endpoint is radial projection to the sphere; inside that radius the radial scale is capped at
`2`, making the endpoint and the deformation continuous at the origin.  The control is the
clamped function `2 * (1 - ‖x‖)`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Topology
open scoped unitInterval

universe u v

namespace TopPair

variable {E : Type v} [NormedAddCommGroup E]

/-- The nonsingular radial scale used for the closed-ball deformation. -/
def closedUnitBallRadialScale (x : E) : ℝ :=
  (max ‖x‖ ((1 : ℝ) / 2))⁻¹

private theorem closedUnitBallRadialScale_pos (x : E) :
    0 < closedUnitBallRadialScale x := by
  apply inv_pos.mpr
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_right _ _)

private theorem continuous_closedUnitBallRadialScale :
    Continuous (closedUnitBallRadialScale : E → ℝ) := by
  apply Continuous.inv₀ (continuous_norm.max continuous_const)
  intro x hx
  have hpos : (0 : ℝ) < max ‖x‖ (1 / 2) :=
    lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  exact hpos.ne' hx

private theorem one_le_closedUnitBallRadialScale {x : E} (hx : ‖x‖ ≤ 1) :
    1 ≤ closedUnitBallRadialScale x := by
  apply (one_le_inv₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
    (le_max_right _ _))).mpr
  exact max_le hx (by norm_num)

private theorem closedUnitBallRadialScale_mul_norm_le_one (x : E) :
    closedUnitBallRadialScale x * ‖x‖ ≤ 1 := by
  by_cases h : ‖x‖ ≤ (1 : ℝ) / 2
  · rw [closedUnitBallRadialScale, max_eq_right h]
    norm_num
    linarith
  · have hhalf : (1 : ℝ) / 2 ≤ ‖x‖ := le_of_not_ge h
    have hnorm : ‖x‖ ≠ 0 := by positivity
    rw [closedUnitBallRadialScale, max_eq_left hhalf, inv_mul_cancel₀ hnorm]

private theorem closedUnitBallRadialScale_eq_one {x : E} (hx : ‖x‖ = 1) :
    closedUnitBallRadialScale x = 1 := by
  rw [closedUnitBallRadialScale, hx, max_eq_left (by norm_num), inv_one]

private theorem closedUnitBallRadialScale_mul_norm_eq_one_of_half_lt
    {x : E} (hx : (1 : ℝ) / 2 < ‖x‖) :
    closedUnitBallRadialScale x * ‖x‖ = 1 := by
  have hnorm : ‖x‖ ≠ 0 := by positivity
  rw [closedUnitBallRadialScale, max_eq_left hx.le, inv_mul_cancel₀ hnorm]

/-- The scalar used at time `t` in the closed-ball radial deformation. -/
def closedUnitBallRadialFactor (t : unitInterval) (x : E) : ℝ :=
  (1 - (t : ℝ)) + (t : ℝ) * closedUnitBallRadialScale x

private theorem one_le_closedUnitBallRadialFactor
    (t : unitInterval) {x : E} (hx : ‖x‖ ≤ 1) :
    1 ≤ closedUnitBallRadialFactor t x := by
  have hs := one_le_closedUnitBallRadialScale hx
  have ht0 := t.property.1
  have hmul : 0 ≤ (t : ℝ) * (closedUnitBallRadialScale x - 1) :=
    mul_nonneg ht0 (sub_nonneg.mpr hs)
  dsimp [closedUnitBallRadialFactor]
  nlinarith

private theorem closedUnitBallRadialFactor_le_scale
    (t : unitInterval) {x : E} (hx : ‖x‖ ≤ 1) :
    closedUnitBallRadialFactor t x ≤ closedUnitBallRadialScale x := by
  have hs := one_le_closedUnitBallRadialScale hx
  have ht1 := t.property.2
  have hmul : 0 ≤ (1 - (t : ℝ)) * (closedUnitBallRadialScale x - 1) :=
    mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hs)
  dsimp [closedUnitBallRadialFactor]
  nlinarith

@[simp]
theorem closedUnitBallRadialFactor_zero (x : E) :
    closedUnitBallRadialFactor 0 x = 1 := by
  simp [closedUnitBallRadialFactor]

@[simp]
theorem closedUnitBallRadialFactor_one (x : E) :
    closedUnitBallRadialFactor 1 x = closedUnitBallRadialScale x := by
  simp [closedUnitBallRadialFactor]

private theorem closedUnitBallRadialFactor_eq_one_of_norm_eq_one
    (t : unitInterval) {x : E} (hx : ‖x‖ = 1) :
    closedUnitBallRadialFactor t x = 1 := by
  rw [closedUnitBallRadialFactor, closedUnitBallRadialScale_eq_one hx]
  ring

private theorem closedUnitBallRadialFactor_mul_norm_le_one
    (t : unitInterval) {x : E} (hx : ‖x‖ ≤ 1) :
    closedUnitBallRadialFactor t x * ‖x‖ ≤ 1 := by
  calc
    closedUnitBallRadialFactor t x * ‖x‖ ≤
        closedUnitBallRadialScale x * ‖x‖ :=
      mul_le_mul_of_nonneg_right (closedUnitBallRadialFactor_le_scale t hx) (norm_nonneg x)
    _ ≤ 1 := closedUnitBallRadialScale_mul_norm_le_one x

private theorem closedBallPair_mem_iff_norm_le
    (z : (closedBallPair.{u} (0 : E) 1).fst) :
    ‖z.down.val‖ ≤ 1 := by
  have hz := z.down.property
  change dist z.down.val (0 : E) ≤ 1 at hz
  simpa only [dist_zero_right] using hz

/-- Membership in the sphere subspace of the closed unit-ball pair, expressed by the norm. -/
theorem mem_range_closedUnitBallPair_map_iff
    (z : (closedBallPair.{u} (0 : E) 1).fst) :
    z ∈ Set.range (closedBallPair.{u} (0 : E) 1).map ↔ ‖z.down.val‖ = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    have hy := y.down.property
    change dist y.down.val (0 : E) = 1 at hy
    have hmap :
        ((closedBallPair.{u} (0 : E) 1).map y).down.val = y.down.val :=
      rfl
    rw [hmap]
    simpa only [dist_zero_right] using hy
  · intro hz
    let y : (closedBallPair.{u} (0 : E) 1).snd :=
      ULift.up ⟨z.down.val, by simpa [Metric.mem_sphere, dist_zero_right] using hz⟩
    refine ⟨y, ?_⟩
    apply ULift.ext
    apply Subtype.ext
    rfl

/-- Control for the sphere inside the closed unit ball. -/
def closedUnitBallControl (E : Type v) [NormedAddCommGroup E] :
    C((closedBallPair.{u} (0 : E) 1).fst, unitInterval) where
  toFun z := Set.projIcc 0 1 zero_le_one (2 * (1 - ‖z.down.val‖))
  continuous_toFun := continuous_projIcc.comp
    (continuous_const.mul (continuous_const.sub
      (continuous_norm.comp
        (continuous_subtype_val.comp continuous_uliftDown))))

@[simp]
theorem closedUnitBallControl_apply
    (z : (closedBallPair.{u} (0 : E) 1).fst) :
    closedUnitBallControl E z =
      Set.projIcc 0 1 zero_le_one (2 * (1 - ‖z.down.val‖)) :=
  rfl

/-- The endpoint of the radial deformation of the closed unit ball. -/
def closedUnitBallEndpoint (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    C((closedBallPair.{u} (0 : E) 1).fst,
      (closedBallPair.{u} (0 : E) 1).fst) where
  toFun z := ULift.up ⟨closedUnitBallRadialScale z.down.val • z.down.val, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (closedUnitBallRadialScale_pos _).le]
    exact closedUnitBallRadialScale_mul_norm_le_one z.down.val⟩
  continuous_toFun := by
    apply continuous_uliftUp.comp
    apply Continuous.subtype_mk
    exact (continuous_closedUnitBallRadialScale.smul continuous_id).comp
      (continuous_subtype_val.comp continuous_uliftDown)

@[simp]
theorem closedUnitBallEndpoint_down_val
    [NormedSpace ℝ E] (z : (closedBallPair.{u} (0 : E) 1).fst) :
    (closedUnitBallEndpoint E z).down.val =
      closedUnitBallRadialScale z.down.val • z.down.val :=
  rfl

/-- The radial deformation of the closed unit ball, capped near the origin. -/
def closedUnitBallDeformationMap
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    C(unitInterval × (closedBallPair.{u} (0 : E) 1).fst,
      (closedBallPair.{u} (0 : E) 1).fst) where
  toFun p := ULift.up
    ⟨closedUnitBallRadialFactor p.1 p.2.down.val • p.2.down.val, by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_of_nonneg
          (zero_le_one.trans (one_le_closedUnitBallRadialFactor p.1
            (closedBallPair_mem_iff_norm_le p.2)))]
      exact closedUnitBallRadialFactor_mul_norm_le_one p.1
        (closedBallPair_mem_iff_norm_le p.2)⟩
  continuous_toFun := by
    apply continuous_uliftUp.comp
    apply Continuous.subtype_mk
    have hpoint : Continuous
        (fun p : unitInterval × (closedBallPair.{u} (0 : E) 1).fst =>
          p.2.down.val) :=
      continuous_subtype_val.comp (continuous_uliftDown.comp continuous_snd)
    have hscale : Continuous
        (fun p : unitInterval × (closedBallPair.{u} (0 : E) 1).fst =>
          closedUnitBallRadialScale p.2.down.val) :=
      continuous_closedUnitBallRadialScale.comp hpoint
    have hfactor : Continuous
        (fun p : unitInterval × (closedBallPair.{u} (0 : E) 1).fst =>
          closedUnitBallRadialFactor p.1 p.2.down.val) := by
      exact (continuous_const.sub
        (continuous_subtype_val.comp continuous_fst)).add
          ((continuous_subtype_val.comp continuous_fst).mul hscale)
    exact hfactor.smul hpoint

@[simp]
theorem closedUnitBallDeformationMap_down_val
    [NormedSpace ℝ E] (t : unitInterval)
    (z : (closedBallPair.{u} (0 : E) 1).fst) :
    (closedUnitBallDeformationMap E (t, z)).down.val =
      closedUnitBallRadialFactor t z.down.val • z.down.val :=
  rfl

/-- The closed unit-ball deformation as a homotopy relative to its sphere. -/
def closedUnitBallDeformation
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContinuousMap.HomotopyRel (ContinuousMap.id (closedBallPair.{u} (0 : E) 1).fst)
      (closedUnitBallEndpoint E)
      (Set.range (closedBallPair.{u} (0 : E) 1).map) where
  toFun := closedUnitBallDeformationMap E
  continuous_toFun := (closedUnitBallDeformationMap E).continuous
  map_zero_left z := by
    apply ULift.ext
    apply Subtype.ext
    simp
  map_one_left z := by
    apply ULift.ext
    apply Subtype.ext
    simp
  prop' t z hz := by
    apply ULift.ext
    apply Subtype.ext
    change closedUnitBallRadialFactor t z.down.val • z.down.val = z.down.val
    rw [closedUnitBallRadialFactor_eq_one_of_norm_eq_one t
      ((mem_range_closedUnitBallPair_map_iff z).mp hz), one_smul]

/-- Controlled NDR data for the sphere inside a closed unit ball. -/
def closedUnitBallNDRData
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NDRData (closedBallPair.{u} (0 : E) 1) where
  control := closedUnitBallControl E
  endpoint := closedUnitBallEndpoint E
  deformation := closedUnitBallDeformation E
  control_eq_zero_iff := fun z => by
    rw [closedUnitBallControl_apply, projIcc_eq_zero]
    have hz := closedBallPair_mem_iff_norm_le z
    rw [mem_range_closedUnitBallPair_map_iff]
    constructor <;> intro h
    · nlinarith
    · nlinarith
  control_deformation_le := fun t z => by
    rw [closedUnitBallControl_apply, closedUnitBallControl_apply]
    apply Set.monotone_projIcc
    change 2 * (1 - ‖closedUnitBallRadialFactor t z.down.val • z.down.val‖) ≤
      2 * (1 - ‖z.down.val‖)
    rw [norm_smul,
      Real.norm_of_nonneg
        (zero_le_one.trans (one_le_closedUnitBallRadialFactor t
          (closedBallPair_mem_iff_norm_le z)))]
    have hfactor := one_le_closedUnitBallRadialFactor t
      (closedBallPair_mem_iff_norm_le z)
    have hnorm := norm_nonneg z.down.val
    nlinarith
  endpoint_mem_range := fun z hz => by
    rw [closedUnitBallControl_apply] at hz
    have hhalf : (1 : ℝ) / 2 < ‖z.down.val‖ := by
      by_contra h
      have hraw : (1 : ℝ) ≤ 2 * (1 - ‖z.down.val‖) := by
        have := le_of_not_gt h
        nlinarith
      have hone : Set.projIcc 0 1 zero_le_one
          (2 * (1 - ‖z.down.val‖)) = 1 :=
        projIcc_eq_one.mpr hraw
      rw [hone] at hz
      exact (lt_irrefl 1 hz).elim
    rw [mem_range_closedUnitBallPair_map_iff,
      closedUnitBallEndpoint_down_val, norm_smul,
      Real.norm_of_nonneg (closedUnitBallRadialScale_pos _).le,
      closedUnitBallRadialScale_mul_norm_eq_one_of_half_lt hhalf]

/-- The sphere inclusion in a closed unit ball is a Hurewicz cofibration. -/
theorem closedUnitBall_isHurewiczCofibration
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    TopCat.IsHurewiczCofibration (closedBallPair.{u} (0 : E) 1).map :=
  (closedUnitBallNDRData.{u} E).toStandard.isHurewiczCofibration

end TopPair

namespace Topology.CWComplex

/-- Controlled NDR data for the boundary of a classical cell. -/
noncomputable def classicalCellDiskPairNDRData (n : ℕ) :
    TopPair.NDRData (classicalCellDiskPair.{u} n) :=
  TopPair.closedUnitBallNDRData.{u} (Fin n → ℝ)

/-- Chosen good-pair data for every positive-dimensional classical cell. -/
noncomputable def classicalCellDiskPairGoodPairData (m : ℕ) :
    TopPair.GoodPairData (classicalCellDiskPair.{u} (m + 1)) :=
  (classicalCellDiskPairNDRData.{u} (m + 1)).toGoodPairData

/-- The boundary inclusion of a classical cell is a Hurewicz cofibration. -/
theorem classicalCellDiskPair_isHurewiczCofibration (n : ℕ) :
    TopCat.IsHurewiczCofibration (classicalCellDiskPair.{u} n).map :=
  TopPair.closedUnitBall_isHurewiczCofibration.{u} (Fin n → ℝ)

end Topology.CWComplex

end
