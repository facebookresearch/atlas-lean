/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.SquareBoundaryPerimeter
public import Mathlib.Topology.Covering.FundamentalGroupCircle
public import Mathlib.Topology.Instances.AddCircle.Real

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The original square perimeter as a circle map

The existing four-edge perimeter descends through identification of its
endpoints to the additive circle of period one. Its four quarter formulas
retain the original max-norm square coordinates and traversal orientation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped unitInterval

universe u

namespace Topology.CWComplex

/-- The actual original perimeter descended to the circle of period one. -/
def classicalCellSquarePerimeterCircleMap :
    C(AddCircle (1 : ℝ), classicalCellSquareBoundary.{u}) := by
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  exact
    { toFun := AddCircle.liftIco (1 : ℝ) 0 classicalCellSquarePerimeter.{u}.extend
      continuous_toFun := by
        exact AddCircle.liftIco_zero_continuous
          ((Path.extend_zero classicalCellSquarePerimeter.{u}).trans
            (Path.extend_one classicalCellSquarePerimeter.{u}).symm)
          classicalCellSquarePerimeter.{u}.continuous_extend.continuousOn }

/-- Before the identified endpoint, the circle map is the same original perimeter path. -/
theorem classicalCellSquarePerimeterCircleMap_coe_lt (t : I) (ht : (t : ℝ) < 1) :
    classicalCellSquarePerimeterCircleMap.{u} (t : AddCircle (1 : ℝ)) =
      classicalCellSquarePerimeter.{u} t := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  change AddCircle.liftIco (1 : ℝ) 0 classicalCellSquarePerimeter.{u}.extend
      (t : AddCircle (1 : ℝ)) = classicalCellSquarePerimeter.{u} t
  exact (AddCircle.liftIco_zero_coe_apply ⟨t.2.1, ht⟩).trans
    (Path.extend_apply classicalCellSquarePerimeter.{u} t.2)

/-- The circle map retains the original perimeter at every time, including the endpoint. -/
theorem classicalCellSquarePerimeterCircleMap_coe (t : I) :
    classicalCellSquarePerimeterCircleMap.{u} (t : AddCircle (1 : ℝ)) =
      classicalCellSquarePerimeter.{u} t := by
  by_cases ht : (t : ℝ) < 1
  · exact classicalCellSquarePerimeterCircleMap_coe_lt t ht
  · have htOne : t = (1 : I) := by
      apply Subtype.ext
      exact le_antisymm t.2.2 (not_lt.mp ht)
    subst t
    have hZero := classicalCellSquarePerimeterCircleMap_coe_lt.{u} (0 : I)
      (by norm_num : ((0 : I) : ℝ) < 1)
    have hEndpoints : classicalCellSquarePerimeter.{u} (0 : I) =
        classicalCellSquarePerimeter.{u} (1 : I) :=
      classicalCellSquarePerimeter.{u}.source.trans classicalCellSquarePerimeter.{u}.target.symm
    simpa only [Set.Icc.coe_zero, Set.Icc.coe_one, AddCircle.coe_zero, AddCircle.coe_period]
      using hZero.trans hEndpoints

/-- The original starting corner is the image of the circle basepoint. -/
theorem classicalCellSquarePerimeterCircleMap_zero :
    classicalCellSquarePerimeterCircleMap.{u} 0 = classicalCellSquareBottomLeft.{u} := by
  have h := classicalCellSquarePerimeterCircleMap_coe.{u} (0 : I)
  simpa only [Set.Icc.coe_zero, AddCircle.coe_zero]
    using h.trans classicalCellSquarePerimeter.{u}.source

/-- The first quarter is the original bottom edge, with its actual perimeter parameter. -/
theorem classicalCellSquarePerimeter_bottom_quarter (t : I)
    (ht : (t : ℝ) ≤ (1 : ℝ) / 4) :
    (classicalCellSquarePerimeter.{u} t).down.val = ![8 * (t : ℝ) - 1, -1] := by
  have hOuter : (t : ℝ) ≤ 1 / 2 := by linarith
  have hInner : 2 * (t : ℝ) ≤ 1 / 2 := by linarith
  rw [classicalCellSquarePerimeter, Path.trans_apply, dite_eq_left hOuter,
    Path.trans_apply, dite_eq_left hInner]
  change (![2 * (2 * (2 * (t : ℝ))) - 1, -1] : Fin 2 → ℝ) =
    ![8 * (t : ℝ) - 1, -1]
  funext i
  fin_cases i
  · norm_num
    ring
  · norm_num

/-- The second quarter is the original right edge. -/
theorem classicalCellSquarePerimeter_right_quarter (t : I)
    (ht₀ : (1 : ℝ) / 4 < (t : ℝ)) (ht₁ : (t : ℝ) ≤ (1 : ℝ) / 2) :
    (classicalCellSquarePerimeter.{u} t).down.val = ![1, 8 * (t : ℝ) - 3] := by
  have hInner : ¬ 2 * (t : ℝ) ≤ 1 / 2 := by linarith
  rw [classicalCellSquarePerimeter, Path.trans_apply, dite_eq_left ht₁,
    Path.trans_apply, dite_eq_right hInner]
  change (![1, 2 * (2 * (2 * (t : ℝ)) - 1) - 1] : Fin 2 → ℝ) =
    ![1, 8 * (t : ℝ) - 3]
  funext i
  fin_cases i
  · norm_num
  · norm_num
    ring

/-- The third quarter is the original top edge, traversed right to left. -/
theorem classicalCellSquarePerimeter_top_quarter (t : I)
    (ht₀ : (1 : ℝ) / 2 < (t : ℝ)) (ht₁ : (t : ℝ) ≤ (3 : ℝ) / 4) :
    (classicalCellSquarePerimeter.{u} t).down.val = ![5 - 8 * (t : ℝ), 1] := by
  have hOuter : ¬ (t : ℝ) ≤ 1 / 2 := by linarith
  have hInner : 2 * (t : ℝ) - 1 ≤ 1 / 2 := by linarith
  rw [classicalCellSquarePerimeter, Path.trans_apply, dite_eq_right hOuter,
    Path.trans_apply, dite_eq_left hInner]
  change (![1 - 2 * (2 * (2 * (t : ℝ) - 1)), 1] : Fin 2 → ℝ) =
    ![5 - 8 * (t : ℝ), 1]
  funext i
  fin_cases i
  · norm_num
    ring
  · norm_num

/-- The last quarter is the original left edge, returning to the starting corner. -/
theorem classicalCellSquarePerimeter_left_quarter (t : I)
    (ht : (3 : ℝ) / 4 < (t : ℝ)) :
    (classicalCellSquarePerimeter.{u} t).down.val = ![-1, 7 - 8 * (t : ℝ)] := by
  have hOuter : ¬ (t : ℝ) ≤ 1 / 2 := by linarith
  have hInner : ¬ 2 * (t : ℝ) - 1 ≤ 1 / 2 := by linarith
  rw [classicalCellSquarePerimeter, Path.trans_apply, dite_eq_right hOuter,
    Path.trans_apply, dite_eq_right hInner]
  change (![-1, 1 - 2 * (2 * (2 * (t : ℝ) - 1) - 1)] : Fin 2 → ℝ) =
    ![-1, 7 - 8 * (t : ℝ)]
  funext i
  fin_cases i
  · norm_num
  · norm_num
    ring

/-- The original perimeter coordinate of a square-boundary point, before identifying endpoints. -/
def classicalCellSquareCircleParameterReal (z : classicalCellSquareBoundary.{u}) : ℝ := by
  classical
  exact if classicalCellSquareCoord 1 z = -1 then (classicalCellSquareCoord 0 z + 1) / 8
    else if classicalCellSquareCoord 0 z = 1 then (classicalCellSquareCoord 1 z + 3) / 8
    else if classicalCellSquareCoord 1 z = 1 then (5 - classicalCellSquareCoord 0 z) / 8
    else (7 - classicalCellSquareCoord 1 z) / 8

/-- The selected real coordinate uses the actual half-open perimeter interval. -/
theorem classicalCellSquareCircleParameterReal_mem (z : classicalCellSquareBoundary.{u}) :
    classicalCellSquareCircleParameterReal z ∈ Set.Ico (0 : ℝ) 1 := by
  classical
  obtain ⟨hx₀, hx₁⟩ := classicalCellSquareCoord_bounds 0 z
  obtain ⟨hy₀, hy₁⟩ := classicalCellSquareCoord_bounds 1 z
  unfold classicalCellSquareCircleParameterReal
  split_ifs with hb hr ht
  · constructor <;> linarith
  · constructor <;> linarith
  · constructor <;> linarith
  · have hy : -1 < classicalCellSquareCoord 1 z := by
      by_contra h
      exact hb (le_antisymm (not_lt.mp h) hy₀)
    constructor <;> linarith

/-- The inverse perimeter coordinate, valued in the original circle of period one. -/
def classicalCellSquareCircleParameter (z : classicalCellSquareBoundary.{u}) :
    AddCircle (1 : ℝ) :=
  (classicalCellSquareCircleParameterReal z : AddCircle (1 : ℝ))

/-- At every un-identified time the real coordinate recovers the exact original parameter. -/
theorem classicalCellSquareCircleParameterReal_perimeter (t : I) (ht : (t : ℝ) < 1) :
    classicalCellSquareCircleParameterReal (classicalCellSquarePerimeter.{u} t) = (t : ℝ) := by
  classical
  by_cases h₀ : (t : ℝ) ≤ (1 : ℝ) / 4
  · have h := classicalCellSquarePerimeter_bottom_quarter.{u} t h₀
    have hx : classicalCellSquareCoord 0 (classicalCellSquarePerimeter.{u} t) =
        8 * (t : ℝ) - 1 := congrArg (fun v : Fin 2 → ℝ => v 0) h
    have hy : classicalCellSquareCoord 1 (classicalCellSquarePerimeter.{u} t) = -1 :=
      congrArg (fun v : Fin 2 → ℝ => v 1) h
    simp only [classicalCellSquareCircleParameterReal, hy, hx, ↓reduceIte]; ring
  by_cases h₁ : (t : ℝ) ≤ (1 : ℝ) / 2
  · have h := classicalCellSquarePerimeter_right_quarter.{u} t (not_le.mp h₀) h₁
    have hx : classicalCellSquareCoord 0 (classicalCellSquarePerimeter.{u} t) = 1 :=
      congrArg (fun v : Fin 2 → ℝ => v 0) h
    have hy : classicalCellSquareCoord 1 (classicalCellSquarePerimeter.{u} t) =
        8 * (t : ℝ) - 3 := congrArg (fun v : Fin 2 → ℝ => v 1) h
    have hb : classicalCellSquareCoord 1 (classicalCellSquarePerimeter.{u} t) ≠ -1 := by
      rw [hy]
      intro h
      linarith
    simp only [classicalCellSquareCircleParameterReal, hb, hx, ↓reduceIte]
    rw [hy]
    ring
  by_cases h₂ : (t : ℝ) ≤ (3 : ℝ) / 4
  · have h := classicalCellSquarePerimeter_top_quarter.{u} t (not_le.mp h₁) h₂
    have hx : classicalCellSquareCoord 0 (classicalCellSquarePerimeter.{u} t) =
        5 - 8 * (t : ℝ) := congrArg (fun v : Fin 2 → ℝ => v 0) h
    have hy : classicalCellSquareCoord 1 (classicalCellSquarePerimeter.{u} t) = 1 :=
      congrArg (fun v : Fin 2 → ℝ => v 1) h
    have hr : classicalCellSquareCoord 0 (classicalCellSquarePerimeter.{u} t) ≠ 1 := by
      rw [hx]
      intro h
      linarith
    have hb : classicalCellSquareCoord 1 (classicalCellSquarePerimeter.{u} t) ≠ -1 := by
      rw [hy]
      norm_num
    simp only [classicalCellSquareCircleParameterReal, hb, hr, ↓reduceIte]
    simp only [hy, ↓reduceIte]
    rw [hx]
    ring
  · have h := classicalCellSquarePerimeter_left_quarter.{u} t (not_le.mp h₂)
    have hx : classicalCellSquareCoord 0 (classicalCellSquarePerimeter.{u} t) = -1 :=
      congrArg (fun v : Fin 2 → ℝ => v 0) h
    have hy : classicalCellSquareCoord 1 (classicalCellSquarePerimeter.{u} t) =
        7 - 8 * (t : ℝ) := congrArg (fun v : Fin 2 → ℝ => v 1) h
    have hb : classicalCellSquareCoord 1 (classicalCellSquarePerimeter.{u} t) ≠ -1 := by
      rw [hy]
      intro h
      linarith
    have ht' : classicalCellSquareCoord 1 (classicalCellSquarePerimeter.{u} t) ≠ 1 := by
      rw [hy]
      intro h
      linarith
    have hr : classicalCellSquareCoord 0 (classicalCellSquarePerimeter.{u} t) ≠ 1 := by
      rw [hx]
      norm_num
    simp only [classicalCellSquareCircleParameterReal, hb, hr, ht', ↓reduceIte]
    rw [hy]
    ring

/-- The identified perimeter coordinate recovers the circle parameter at every time. -/
theorem classicalCellSquareCircleParameter_perimeter (t : I) :
    classicalCellSquareCircleParameter (classicalCellSquarePerimeter.{u} t) =
      (t : AddCircle (1 : ℝ)) := by
  by_cases ht : (t : ℝ) < 1
  · exact congrArg (fun r : ℝ => (r : AddCircle (1 : ℝ)))
      (classicalCellSquareCircleParameterReal_perimeter t ht)
  · have htOne : t = (1 : I) := by
      apply Subtype.ext
      exact le_antisymm t.2.2 (not_lt.mp ht)
    subst t
    have h := classicalCellSquareCircleParameterReal_perimeter.{u} (0 : I)
      (by norm_num : ((0 : I) : ℝ) < 1)
    have hEndpoints : classicalCellSquarePerimeter.{u} (1 : I) =
        classicalCellSquarePerimeter.{u} (0 : I) :=
      classicalCellSquarePerimeter.{u}.target.trans classicalCellSquarePerimeter.{u}.source.symm
    have hParameter : classicalCellSquareCircleParameter
        (classicalCellSquarePerimeter.{u} (1 : I)) = (0 : AddCircle (1 : ℝ)) :=
      (congrArg classicalCellSquareCircleParameter hEndpoints).trans
        (congrArg (fun r : ℝ => (r : AddCircle (1 : ℝ))) h)
    simpa only [AddCircle.coe_zero, AddCircle.coe_period] using hParameter

/-- The selected original perimeter time, retaining its actual interval bound. -/
def classicalCellSquarePerimeterParameter (z : classicalCellSquareBoundary.{u}) : I :=
  ⟨classicalCellSquareCircleParameterReal z,
    (classicalCellSquareCircleParameterReal_mem z).1,
    (classicalCellSquareCircleParameterReal_mem z).2.le⟩

/-- The original four-edge perimeter reconstructs every original square-boundary point. -/
theorem classicalCellSquarePerimeter_parameter (z : classicalCellSquareBoundary.{u}) :
    classicalCellSquarePerimeter.{u} (classicalCellSquarePerimeterParameter z) = z := by
  classical
  apply ULift.down_injective
  apply Subtype.ext
  obtain ⟨hx₀, hx₁⟩ := classicalCellSquareCoord_bounds 0 z
  obtain ⟨hy₀, hy₁⟩ := classicalCellSquareCoord_bounds 1 z
  by_cases hb : classicalCellSquareCoord 1 z = -1
  · have hv : (classicalCellSquarePerimeterParameter z : ℝ) =
        (classicalCellSquareCoord 0 z + 1) / 8 := by
      simp only [classicalCellSquarePerimeterParameter, classicalCellSquareCircleParameterReal,
        hb, ↓reduceIte]
    have ht : (classicalCellSquarePerimeterParameter z : ℝ) ≤ (1 : ℝ) / 4 := by
      rw [hv]
      linarith
    have h := classicalCellSquarePerimeter_bottom_quarter.{u}
      (classicalCellSquarePerimeterParameter z) ht
    apply h.trans
    funext i
    fin_cases i
    · change 8 * (classicalCellSquarePerimeterParameter z : ℝ) - 1 =
        classicalCellSquareCoord 0 z
      rw [hv]
      ring
    · change (-1 : ℝ) = classicalCellSquareCoord 1 z
      exact hb.symm
  by_cases hr : classicalCellSquareCoord 0 z = 1
  · have hv : (classicalCellSquarePerimeterParameter z : ℝ) =
        (classicalCellSquareCoord 1 z + 3) / 8 := by
      simp only [classicalCellSquarePerimeterParameter, classicalCellSquareCircleParameterReal,
        hb, hr, ↓reduceIte]
    have hy : -1 < classicalCellSquareCoord 1 z := by
      by_contra h
      exact hb (le_antisymm (not_lt.mp h) hy₀)
    have ht₀ : (1 : ℝ) / 4 < (classicalCellSquarePerimeterParameter z : ℝ) := by
      rw [hv]
      linarith
    have ht₁ : (classicalCellSquarePerimeterParameter z : ℝ) ≤ (1 : ℝ) / 2 := by
      rw [hv]
      linarith
    have h := classicalCellSquarePerimeter_right_quarter.{u}
      (classicalCellSquarePerimeterParameter z) ht₀ ht₁
    apply h.trans
    funext i
    fin_cases i
    · change (1 : ℝ) = classicalCellSquareCoord 0 z
      exact hr.symm
    · change 8 * (classicalCellSquarePerimeterParameter z : ℝ) - 3 =
        classicalCellSquareCoord 1 z
      rw [hv]
      ring
  by_cases ht : classicalCellSquareCoord 1 z = 1
  · have hv : (classicalCellSquarePerimeterParameter z : ℝ) =
        (5 - classicalCellSquareCoord 0 z) / 8 := by
      change classicalCellSquareCircleParameterReal z = (5 - classicalCellSquareCoord 0 z) / 8
      simp only [classicalCellSquareCircleParameterReal, hb, hr, ↓reduceIte]
      simp only [ht, ↓reduceIte]
    have hx : classicalCellSquareCoord 0 z < 1 := by
      by_contra h
      exact hr (le_antisymm hx₁ (not_lt.mp h))
    have ht₀ : (1 : ℝ) / 2 < (classicalCellSquarePerimeterParameter z : ℝ) := by
      rw [hv]
      linarith
    have ht₁ : (classicalCellSquarePerimeterParameter z : ℝ) ≤ (3 : ℝ) / 4 := by
      rw [hv]
      linarith
    have h := classicalCellSquarePerimeter_top_quarter.{u}
      (classicalCellSquarePerimeterParameter z) ht₀ ht₁
    apply h.trans
    funext i
    fin_cases i
    · change 5 - 8 * (classicalCellSquarePerimeterParameter z : ℝ) =
        classicalCellSquareCoord 0 z
      rw [hv]
      ring
    · change (1 : ℝ) = classicalCellSquareCoord 1 z
      exact ht.symm
  · have hv : (classicalCellSquarePerimeterParameter z : ℝ) =
        (7 - classicalCellSquareCoord 1 z) / 8 := by
      simp only [classicalCellSquarePerimeterParameter, classicalCellSquareCircleParameterReal,
        hb, hr, ht, ↓reduceIte]
    have hx : classicalCellSquareCoord 0 z = -1 := by
      rcases classicalCellSquare_edge_cover z with h | h
      · exact (hb h).elim
      · rcases h with h | h | h
        · exact h
        · exact (hr h).elim
        · exact (ht h).elim
    have hy : classicalCellSquareCoord 1 z < 1 := by
      by_contra h
      exact ht (le_antisymm hy₁ (not_lt.mp h))
    have ht' : (3 : ℝ) / 4 < (classicalCellSquarePerimeterParameter z : ℝ) := by
      rw [hv]
      linarith
    have h := classicalCellSquarePerimeter_left_quarter.{u}
      (classicalCellSquarePerimeterParameter z) ht'
    apply h.trans
    funext i
    fin_cases i
    · change (-1 : ℝ) = classicalCellSquareCoord 0 z
      exact hx.symm
    · change 7 - 8 * (classicalCellSquarePerimeterParameter z : ℝ) =
        classicalCellSquareCoord 1 z
      rw [hv]
      ring

/-- The circle map of the selected coordinate is the same original boundary point. -/
theorem classicalCellSquarePerimeterCircleMap_parameter
    (z : classicalCellSquareBoundary.{u}) :
    classicalCellSquarePerimeterCircleMap.{u} (classicalCellSquareCircleParameter z) = z :=
  (classicalCellSquarePerimeterCircleMap_coe (classicalCellSquarePerimeterParameter z)).trans
    (classicalCellSquarePerimeter_parameter z)

/-- The original boundary coordinate is a left inverse of the descended circle map. -/
theorem classicalCellSquareCircleParameter_circleMap (c : AddCircle (1 : ℝ)) :
    classicalCellSquareCircleParameter (classicalCellSquarePerimeterCircleMap.{u} c) = c := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let r := AddCircle.equivIco (1 : ℝ) 0 c
  have hr : (r : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
    simpa only [zero_add] using r.2
  let t : I := ⟨(r : ℝ), hr.1, hr.2.le⟩
  have hc : (t : AddCircle (1 : ℝ)) = c :=
    AddCircle.coe_equivIco
  have hp : classicalCellSquarePerimeterCircleMap.{u} c =
      classicalCellSquarePerimeter.{u} t :=
    (congrArg classicalCellSquarePerimeterCircleMap hc.symm).trans
      (classicalCellSquarePerimeterCircleMap_coe t)
  exact (congrArg classicalCellSquareCircleParameter hp).trans
    ((classicalCellSquareCircleParameter_perimeter t).trans hc)

/-- The actual circle/perimeter equivalence uses the proved original coordinate inverse. -/
def classicalCellSquarePerimeterCircleEquiv :
    AddCircle (1 : ℝ) ≃ classicalCellSquareBoundary.{u} where
  toFun := classicalCellSquarePerimeterCircleMap
  invFun := classicalCellSquareCircleParameter
  left_inv := classicalCellSquareCircleParameter_circleMap
  right_inv := classicalCellSquarePerimeterCircleMap_parameter

/-- The actual square boundary is the circle, with its original four-edge perimeter parameter. -/
def classicalCellSquarePerimeterCircleHomeomorph :
    AddCircle (1 : ℝ) ≃ₜ classicalCellSquareBoundary.{u} := by
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  letI : T2Space classicalCellSquareBoundary.{u} := by
    change T2Space (ULift.{u} (Metric.sphere (0 : Fin 2 → ℝ) 1))
    infer_instance
  exact classicalCellSquarePerimeterCircleEquiv.toHomeomorphOfContinuousClosed
    classicalCellSquarePerimeterCircleMap.continuous
    classicalCellSquarePerimeterCircleMap.continuous.isClosedMap

/-- The forward boundary homeomorphism is exactly the descended original perimeter map. -/
theorem classicalCellSquarePerimeterCircleHomeomorph_apply (c : AddCircle (1 : ℝ)) :
    classicalCellSquarePerimeterCircleHomeomorph.{u} c =
      classicalCellSquarePerimeterCircleMap.{u} c :=
  rfl

/-- The inverse boundary homeomorphism is exactly the original piecewise perimeter coordinate. -/
theorem classicalCellSquarePerimeterCircleHomeomorph_symm_apply
    (z : classicalCellSquareBoundary.{u}) :
    classicalCellSquarePerimeterCircleHomeomorph.{u}.symm z =
      classicalCellSquareCircleParameter z :=
  rfl

/-- The inverse homeomorphism sends the original perimeter to its exact circle time. -/
theorem classicalCellSquarePerimeterCircleHomeomorph_symm_perimeter (t : I) :
    classicalCellSquarePerimeterCircleHomeomorph.{u}.symm
        (classicalCellSquarePerimeter.{u} t) = (t : AddCircle (1 : ℝ)) :=
  classicalCellSquareCircleParameter_perimeter t

/-- The actual circle basepoint is the original bottom-left square corner. -/
theorem classicalCellSquarePerimeterCircleHomeomorph_zero :
    classicalCellSquarePerimeterCircleHomeomorph.{u} 0 = classicalCellSquareBottomLeft.{u} :=
  classicalCellSquarePerimeterCircleMap_zero

/-- The original bottom-left corner has circle coordinate zero. -/
theorem classicalCellSquarePerimeterCircleHomeomorph_symm_bottomLeft :
    classicalCellSquarePerimeterCircleHomeomorph.{u}.symm
      classicalCellSquareBottomLeft.{u} = 0 := by
  have h := congrArg classicalCellSquareCircleParameter classicalCellSquarePerimeter.{u}.source
  have hp := classicalCellSquareCircleParameter_perimeter.{u} (0 : I)
  exact h.symm.trans hp

end Topology.CWComplex

end

end
