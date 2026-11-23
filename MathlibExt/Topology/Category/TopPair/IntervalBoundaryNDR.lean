/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.NDRCofibration
import Mathlib.Topology.Order.ProjIcc

/-!
# NDR data for the boundary of the unit interval

This file constructs controlled deformation data for the pair
`({0,1} ⊆ I)`. The control has a level-one plateau, which permits a
continuous endpoint map to interpolate between the two boundary points.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Topology
open scoped unitInterval

namespace TopPair

/-- The two endpoints of the ordinary unit interval. -/
def intervalBoundary : Set unitInterval :=
  {0, 1}

/-- The literal pair `({0,1} ⊆ [0,1])` in universe zero, used for the
piecewise-linear coordinate construction. -/
abbrev unitIntervalBoundaryPair : TopPair :=
  TopPair.ofSubset (X := TopCat.of unitInterval) intervalBoundary

/-- Piecewise-linear endpoint map. It is zero on the left third, one on the
right third, and interpolates across the middle third. -/
def intervalBoundaryEndpoint : C(unitInterval, unitInterval) where
  toFun t := Set.projIcc 0 1 zero_le_one (3 * (t : ℝ) - 1)
  continuous_toFun := continuous_projIcc.comp
    ((continuous_const.mul continuous_subtype_val).sub continuous_const)

/-- Control for the interval-boundary pair. Its value is one throughout the
middle third. -/
def intervalBoundaryControl : C(unitInterval, unitInterval) where
  toFun t := Set.projIcc 0 1 zero_le_one
    (3 * min (t : ℝ) (1 - (t : ℝ)))
  continuous_toFun := continuous_projIcc.comp
    (continuous_const.mul
      (continuous_subtype_val.min
        (continuous_const.sub continuous_subtype_val)))

@[simp]
theorem intervalBoundaryEndpoint_zero :
    intervalBoundaryEndpoint 0 = 0 := by
  apply Subtype.ext
  simp [intervalBoundaryEndpoint]

@[simp]
theorem intervalBoundaryEndpoint_one :
    intervalBoundaryEndpoint 1 = 1 := by
  apply Subtype.ext
  simp [intervalBoundaryEndpoint]
  norm_num

theorem intervalBoundaryEndpoint_eq_zero_of_le
    (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 3) :
    intervalBoundaryEndpoint t = 0 := by
  change Set.projIcc 0 1 zero_le_one (3 * (t : ℝ) - 1) = 0
  apply projIcc_eq_zero.mpr
  nlinarith

theorem intervalBoundaryEndpoint_eq_one_of_le
    (t : unitInterval) (ht : 2 / 3 ≤ (t : ℝ)) :
    intervalBoundaryEndpoint t = 1 := by
  change Set.projIcc 0 1 zero_le_one (3 * (t : ℝ) - 1) = 1
  apply projIcc_eq_one.mpr
  nlinarith

theorem intervalBoundaryControl_eq_one
    (t : unitInterval) (hleft : 1 / 3 ≤ (t : ℝ))
    (hright : (t : ℝ) ≤ 2 / 3) :
    intervalBoundaryControl t = 1 := by
  change Set.projIcc 0 1 zero_le_one
      (3 * min (t : ℝ) (1 - (t : ℝ))) = 1
  apply projIcc_eq_one.mpr
  have hmin : 1 / 3 ≤ min (t : ℝ) (1 - (t : ℝ)) := by
    apply le_min hleft
    nlinarith
  nlinarith

theorem intervalBoundaryControl_eq_zero_iff (t : unitInterval) :
    intervalBoundaryControl t = 0 ↔ t = 0 ∨ t = 1 := by
  change Set.projIcc 0 1 zero_le_one
      (3 * min (t : ℝ) (1 - (t : ℝ))) = 0 ↔ _
  rw [projIcc_eq_zero]
  constructor
  · intro h
    have hnonneg : 0 ≤ min (t : ℝ) (1 - (t : ℝ)) := by
      exact le_min t.2.1 (sub_nonneg.mpr t.2.2)
    have hmin : min (t : ℝ) (1 - (t : ℝ)) = 0 := by
      nlinarith
    rcases le_total (t : ℝ) (1 - (t : ℝ)) with ht | ht
    · left
      apply Subtype.ext
      rw [min_eq_left ht] at hmin
      exact hmin
    · right
      apply Subtype.ext
      rw [min_eq_right ht] at hmin
      dsimp
      nlinarith
  · rintro (rfl | rfl) <;> norm_num

theorem mem_range_unitIntervalBoundaryPair_map_iff (t : unitInterval) :
    t ∈ Set.range unitIntervalBoundaryPair.map ↔ t = 0 ∨ t = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    change x.1 = 0 ∨ x.1 = 1
    simpa [intervalBoundary] using x.2
  · rintro (rfl | rfl)
    · exact ⟨⟨0, by simp [intervalBoundary]⟩, rfl⟩
    · exact ⟨⟨1, by simp [intervalBoundary]⟩, rfl⟩

theorem intervalBoundaryEndpoint_mem_range (t : unitInterval)
    (ht : intervalBoundaryControl t < 1) :
    intervalBoundaryEndpoint t ∈ Set.range unitIntervalBoundaryPair.map := by
  rw [mem_range_unitIntervalBoundaryPair_map_iff]
  by_cases hleft : (t : ℝ) ≤ 1 / 3
  · left
    exact intervalBoundaryEndpoint_eq_zero_of_le t hleft
  by_cases hright : 2 / 3 ≤ (t : ℝ)
  · right
    exact intervalBoundaryEndpoint_eq_one_of_le t hright
  exfalso
  have hcontrol := intervalBoundaryControl_eq_one t
    (by exact le_of_not_ge hleft) (by exact le_of_not_ge hright)
  rw [hcontrol] at ht
  exact (lt_irrefl 1 ht)

/-- Linear interpolation from the identity to the endpoint map. -/
def intervalBoundaryDeformationMap :
    C(unitInterval × unitInterval, unitInterval) where
  toFun p := Set.Icc.convexComb p.2 (intervalBoundaryEndpoint p.2) p.1
  continuous_toFun := Set.Icc.continuous_convexComb_prod.comp
    (continuous_snd.prodMk
      ((intervalBoundaryEndpoint.continuous.comp continuous_snd).prodMk
        continuous_fst))

/-- The interval deformation, relative to both endpoints. -/
def intervalBoundaryDeformation :
    ContinuousMap.HomotopyRel (ContinuousMap.id unitInterval)
      intervalBoundaryEndpoint
      (Set.range unitIntervalBoundaryPair.map) where
  toFun p := intervalBoundaryDeformationMap p
  continuous_toFun := intervalBoundaryDeformationMap.continuous
  map_zero_left t := by
    exact Set.Icc.convexComb_zero _ _
  map_one_left t := by
    exact Set.Icc.convexComb_one _ _
  prop' s t ht := by
    rcases ht with ⟨t, rfl⟩
    have ht' : t.1 = 0 ∨ t.1 = 1 := by
      simpa [intervalBoundary] using t.2
    rcases ht' with ht | ht
    · have ht0 : t.1 = (0 : unitInterval) := ht
      change Set.Icc.convexComb t.1 (intervalBoundaryEndpoint t.1) s = t.1
      rw [ht0, intervalBoundaryEndpoint_zero, Set.Icc.convexComb_eq]
    · have ht1 : t.1 = (1 : unitInterval) := ht
      change Set.Icc.convexComb t.1 (intervalBoundaryEndpoint t.1) s = t.1
      rw [ht1, intervalBoundaryEndpoint_one, Set.Icc.convexComb_eq]

theorem intervalBoundaryControl_deformation_le
    (s t : unitInterval) :
    intervalBoundaryControl (intervalBoundaryDeformation (s, t)) ≤
      intervalBoundaryControl t := by
  by_cases hleft : (t : ℝ) ≤ 1 / 3
  · rw [show intervalBoundaryDeformation (s, t) =
        Set.Icc.convexComb t 0 s by
      change Set.Icc.convexComb t (intervalBoundaryEndpoint t) s = _
      rw [intervalBoundaryEndpoint_eq_zero_of_le t hleft]]
    change Set.projIcc 0 1 zero_le_one
        (3 * min (Set.Icc.convexComb t 0 s : ℝ)
          (1 - (Set.Icc.convexComb t 0 s : ℝ))) ≤
      Set.projIcc 0 1 zero_le_one
        (3 * min (t : ℝ) (1 - (t : ℝ)))
    apply Set.monotone_projIcc
    have hy : (Set.Icc.convexComb t 0 s : ℝ) ≤ (t : ℝ) := by
      rw [Set.Icc.coe_convexComb]
      norm_num
      nlinarith [mul_nonneg s.2.1 t.2.1]
    have hyhalf : (Set.Icc.convexComb t 0 s : ℝ) ≤
        1 - (Set.Icc.convexComb t 0 s : ℝ) := by
      have hy0 : 0 ≤ (Set.Icc.convexComb t 0 s : ℝ) :=
        (Set.Icc.convexComb t 0 s).2.1
      nlinarith
    have hthalf : (t : ℝ) ≤ 1 - (t : ℝ) := by
      nlinarith
    rw [min_eq_left hyhalf, min_eq_left hthalf]
    nlinarith
  by_cases hright : 2 / 3 ≤ (t : ℝ)
  · rw [show intervalBoundaryDeformation (s, t) =
        Set.Icc.convexComb t 1 s by
      change Set.Icc.convexComb t (intervalBoundaryEndpoint t) s = _
      rw [intervalBoundaryEndpoint_eq_one_of_le t hright]]
    change Set.projIcc 0 1 zero_le_one
        (3 * min (Set.Icc.convexComb t 1 s : ℝ)
          (1 - (Set.Icc.convexComb t 1 s : ℝ))) ≤
      Set.projIcc 0 1 zero_le_one
        (3 * min (t : ℝ) (1 - (t : ℝ)))
    apply Set.monotone_projIcc
    have hy : (t : ℝ) ≤ (Set.Icc.convexComb t 1 s : ℝ) := by
      rw [Set.Icc.coe_convexComb]
      norm_num
      nlinarith [mul_nonneg s.2.1 (sub_nonneg.mpr t.2.2)]
    have hyhalf : 1 - (Set.Icc.convexComb t 1 s : ℝ) ≤
        (Set.Icc.convexComb t 1 s : ℝ) := by
      have hy1 : (Set.Icc.convexComb t 1 s : ℝ) ≤ 1 :=
        (Set.Icc.convexComb t 1 s).2.2
      nlinarith
    have hthalf : 1 - (t : ℝ) ≤ (t : ℝ) := by
      nlinarith
    rw [min_eq_right hyhalf, min_eq_right hthalf]
    nlinarith
  · rw [intervalBoundaryControl_eq_one t
      (le_of_not_ge hleft) (le_of_not_ge hright)]
    exact unitInterval.le_one _

/-- Controlled NDR data for the literal universe-zero coordinate pair. -/
def unitIntervalBoundaryNDRData : NDRData unitIntervalBoundaryPair where
  control := intervalBoundaryControl
  endpoint := intervalBoundaryEndpoint
  deformation := intervalBoundaryDeformation
  control_eq_zero_iff t :=
    (intervalBoundaryControl_eq_zero_iff t).trans
      (mem_range_unitIntervalBoundaryPair_map_iff t).symm
  control_deformation_le := intervalBoundaryControl_deformation_le
  endpoint_mem_range := intervalBoundaryEndpoint_mem_range

universe u

/-- The endpoints in Mathlib's universe-polymorphic interval object. -/
def topCatIntervalBoundary : Set TopCat.I.{u} :=
  {0, 1}

/-- The endpoint pair in the same universe as an arbitrary topological pair. -/
abbrev intervalBoundaryPair : TopPair.{u} :=
  TopPair.ofSubset (X := TopCat.I.{u}) topCatIntervalBoundary

/-- The plateau control transported to `TopCat.I`. -/
def topCatIntervalBoundaryControl : C(TopCat.I.{u}, unitInterval) where
  toFun t := intervalBoundaryControl (TopCat.I.homeomorph t)
  continuous_toFun := intervalBoundaryControl.continuous.comp
    TopCat.I.homeomorph.continuous

/-- The endpoint map transported to `TopCat.I`. -/
def topCatIntervalBoundaryEndpoint : C(TopCat.I.{u}, TopCat.I.{u}) where
  toFun t := TopCat.I.homeomorph.symm
    (intervalBoundaryEndpoint (TopCat.I.homeomorph t))
  continuous_toFun := TopCat.I.homeomorph.symm.continuous.comp
    (intervalBoundaryEndpoint.continuous.comp
      TopCat.I.homeomorph.continuous)

/-- The interval deformation transported to `TopCat.I`. -/
def topCatIntervalBoundaryDeformationMap :
    C(unitInterval × TopCat.I.{u}, TopCat.I.{u}) where
  toFun p := TopCat.I.homeomorph.symm
    (intervalBoundaryDeformation (p.1, TopCat.I.homeomorph p.2))
  continuous_toFun := TopCat.I.homeomorph.symm.continuous.comp
    (intervalBoundaryDeformation.continuous.comp
      (continuous_fst.prodMk
        (TopCat.I.homeomorph.continuous.comp continuous_snd)))

@[simp]
theorem topCatIntervalBoundaryControl_apply (t : TopCat.I.{u}) :
    topCatIntervalBoundaryControl t =
      intervalBoundaryControl (TopCat.I.homeomorph t) :=
  rfl

@[simp]
theorem topCatIntervalBoundaryEndpoint_apply (t : TopCat.I.{u}) :
    topCatIntervalBoundaryEndpoint t = TopCat.I.homeomorph.symm
      (intervalBoundaryEndpoint (TopCat.I.homeomorph t)) :=
  rfl

@[simp]
theorem topCatIntervalBoundaryDeformationMap_apply
    (s : unitInterval) (t : TopCat.I.{u}) :
    topCatIntervalBoundaryDeformationMap (s, t) =
      TopCat.I.homeomorph.symm
        (intervalBoundaryDeformation (s, TopCat.I.homeomorph t)) :=
  rfl

theorem mem_range_intervalBoundaryPair_map_iff (t : TopCat.I.{u}) :
    t ∈ Set.range (intervalBoundaryPair.{u}).map ↔ t = 0 ∨ t = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    change x.1 = 0 ∨ x.1 = 1
    simpa [topCatIntervalBoundary] using x.2
  · rintro (rfl | rfl)
    · exact ⟨⟨0, by simp [topCatIntervalBoundary]⟩, rfl⟩
    · exact ⟨⟨1, by simp [topCatIntervalBoundary]⟩, rfl⟩

/-- The transported interval deformation, relative to both endpoints. -/
def topCatIntervalBoundaryDeformation :
    ContinuousMap.HomotopyRel (ContinuousMap.id TopCat.I.{u})
      topCatIntervalBoundaryEndpoint
      (Set.range (intervalBoundaryPair.{u}).map) where
  toFun p := topCatIntervalBoundaryDeformationMap p
  continuous_toFun := topCatIntervalBoundaryDeformationMap.continuous
  map_zero_left t := by
    rw [topCatIntervalBoundaryDeformationMap_apply]
    rw [intervalBoundaryDeformation.apply_zero]
    exact TopCat.I.homeomorph.symm_apply_apply t
  map_one_left t := by
    rw [topCatIntervalBoundaryDeformationMap_apply,
      topCatIntervalBoundaryEndpoint_apply]
    rw [intervalBoundaryDeformation.apply_one]
  prop' s t ht := by
    have ht' := (mem_range_intervalBoundaryPair_map_iff t).1 ht
    rcases ht' with rfl | rfl
    · change topCatIntervalBoundaryDeformationMap (s, 0) = 0
      rw [topCatIntervalBoundaryDeformationMap_apply]
      rw [TopCat.I.homeomorph_zero]
      have hzero : (0 : unitInterval) ∈
          Set.range unitIntervalBoundaryPair.map :=
        (mem_range_unitIntervalBoundaryPair_map_iff 0).2 (Or.inl rfl)
      rw [intervalBoundaryDeformation.eq_fst s hzero]
      exact TopCat.I.homeomorph.symm_apply_apply 0
    · change topCatIntervalBoundaryDeformationMap (s, 1) = 1
      rw [topCatIntervalBoundaryDeformationMap_apply]
      rw [TopCat.I.homeomorph_one]
      have hone : (1 : unitInterval) ∈
          Set.range unitIntervalBoundaryPair.map :=
        (mem_range_unitIntervalBoundaryPair_map_iff 1).2 (Or.inr rfl)
      rw [intervalBoundaryDeformation.eq_fst s hone]
      exact TopCat.I.homeomorph.symm_apply_apply 1

@[simp]
theorem topCatIntervalBoundaryDeformation_apply
    (s : unitInterval) (t : TopCat.I.{u}) :
    topCatIntervalBoundaryDeformation (s, t) =
      TopCat.I.homeomorph.symm
        (intervalBoundaryDeformation (s, TopCat.I.homeomorph t)) :=
  rfl

theorem topCatIntervalBoundaryControl_eq_zero_iff
    (t : TopCat.I.{u}) :
    topCatIntervalBoundaryControl t = 0 ↔
      t ∈ Set.range (intervalBoundaryPair.{u}).map := by
  rw [topCatIntervalBoundaryControl_apply,
    intervalBoundaryControl_eq_zero_iff,
    mem_range_intervalBoundaryPair_map_iff]
  constructor
  · rintro (ht | ht)
    · left
      apply TopCat.I.ext
      simpa using ht
    · right
      apply TopCat.I.ext
      simpa using ht
  · rintro (rfl | rfl) <;> simp

theorem topCatIntervalBoundaryControl_deformation_le
    (s : unitInterval) (t : TopCat.I.{u}) :
    topCatIntervalBoundaryControl
        (topCatIntervalBoundaryDeformation (s, t)) ≤
      topCatIntervalBoundaryControl t := by
  rw [topCatIntervalBoundaryControl_apply,
    topCatIntervalBoundaryDeformation_apply,
    TopCat.I.homeomorph.apply_symm_apply,
    topCatIntervalBoundaryControl_apply]
  exact intervalBoundaryControl_deformation_le s
    (TopCat.I.homeomorph t)

theorem topCatIntervalBoundaryEndpoint_mem_range
    (t : TopCat.I.{u}) (ht : topCatIntervalBoundaryControl t < 1) :
    topCatIntervalBoundaryEndpoint t ∈
      Set.range (intervalBoundaryPair.{u}).map := by
  rw [topCatIntervalBoundaryControl_apply] at ht
  have h := intervalBoundaryEndpoint_mem_range
    (TopCat.I.homeomorph t) ht
  rw [mem_range_unitIntervalBoundaryPair_map_iff] at h
  rw [mem_range_intervalBoundaryPair_map_iff]
  rcases h with h | h
  · left
    apply TopCat.I.ext
    simpa [topCatIntervalBoundaryEndpoint] using h
  · right
    apply TopCat.I.ext
    simpa [topCatIntervalBoundaryEndpoint] using h

/-- Controlled NDR data for the endpoints of `TopCat.I`, universe-polymorphic
so that it can be combined with arbitrary pairs by `NDRData.prod`. -/
def intervalBoundaryNDRData : NDRData (intervalBoundaryPair.{u}) where
  control := topCatIntervalBoundaryControl
  endpoint := topCatIntervalBoundaryEndpoint
  deformation := topCatIntervalBoundaryDeformation
  control_eq_zero_iff := topCatIntervalBoundaryControl_eq_zero_iff
  control_deformation_le := topCatIntervalBoundaryControl_deformation_le
  endpoint_mem_range := topCatIntervalBoundaryEndpoint_mem_range

/-- The endpoint inclusion in `TopCat.I` is a Hurewicz cofibration in every
universe. -/
theorem intervalBoundary_isHurewiczCofibration :
    TopCat.IsHurewiczCofibration (intervalBoundaryPair.{u}).map :=
  (intervalBoundaryNDRData.{u}).toStandard.isHurewiczCofibration

end TopPair

end
