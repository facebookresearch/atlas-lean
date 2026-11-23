/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.SquareBoundaryLoopMap
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The perimeter of the original classical two-cell

Four paths traverse the bottom, right, top and left edges of the original
max-norm square. Their concatenation is a based boundary loop. The boundary
map associated to a based loop sends the bottom path to that loop and the
other three paths to constant paths, with the actual endpoint casts. The
induced map on the original fundamental groups therefore sends the perimeter
class to the original loop class.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped unitInterval

universe u v

namespace Topology.CWComplex

private theorem classicalCellSquare_mem_of_bounds (a b : ℝ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hface : |a| = 1 ∨ |b| = 1) :
    (![a, b] : Fin 2 → ℝ) ∈ Metric.sphere 0 1 := by
  have hle : ‖(![a, b] : Fin 2 → ℝ)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i
    · change ‖a‖ ≤ 1
      simpa only [Real.norm_eq_abs] using ha
    · change ‖b‖ ≤ 1
      simpa only [Real.norm_eq_abs] using hb
  have hge : 1 ≤ ‖(![a, b] : Fin 2 → ℝ)‖ := by
    rcases hface with h | h
    · have hi := norm_le_pi_norm (![a, b] : Fin 2 → ℝ) (0 : Fin 2)
      change ‖a‖ ≤ ‖(![a, b] : Fin 2 → ℝ)‖ at hi
      simpa only [Real.norm_eq_abs, h] using hi
    · have hi := norm_le_pi_norm (![a, b] : Fin 2 → ℝ) (1 : Fin 2)
      change ‖b‖ ≤ ‖(![a, b] : Fin 2 → ℝ)‖ at hi
      simpa only [Real.norm_eq_abs, h] using hi
  simpa only [Metric.mem_sphere, dist_zero_right] using le_antisymm hle hge

private theorem classicalCellSquare_twice_sub_one_bound (t : I) :
    |2 * (t : ℝ) - 1| ≤ 1 := by
  apply abs_le.mpr
  constructor <;> linarith [unitInterval.nonneg t, unitInterval.le_one t]

private theorem classicalCellSquare_one_sub_twice_bound (t : I) :
    |1 - 2 * (t : ℝ)| ≤ 1 := by
  apply abs_le.mpr
  constructor <;> linarith [unitInterval.nonneg t, unitInterval.le_one t]

private theorem continuous_classicalCellSquare_point (a b : I → ℝ)
    (ha : Continuous a) (hb : Continuous b)
    (h : ∀ t, (![a t, b t] : Fin 2 → ℝ) ∈ Metric.sphere 0 1) :
    Continuous (fun t =>
      (ULift.up ⟨![a t, b t], h t⟩ : classicalCellSquareBoundary.{u})) := by
  have hv : Continuous (fun t : I => (![a t, b t] : Fin 2 → ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact ha
    · exact hb
  exact continuous_uliftUp.comp (hv.subtype_mk h)

/-- The bottom edge of the original square, traversed from left to right. -/
def classicalCellSquareBottomPath :
    Path classicalCellSquareBottomLeft.{u} classicalCellSquareBottomRight.{u} where
  toFun t := ULift.up ⟨![2 * (t : ℝ) - 1, -1], by
    exact classicalCellSquare_mem_of_bounds _ _
      (classicalCellSquare_twice_sub_one_bound t) (by norm_num) (Or.inr (by norm_num))⟩
  continuous_toFun := by
    exact continuous_classicalCellSquare_point (fun t => 2 * (t : ℝ) - 1) (fun _ => -1)
      ((continuous_const.mul continuous_subtype_val).sub continuous_const) continuous_const
      (fun t => classicalCellSquare_mem_of_bounds _ _
        (classicalCellSquare_twice_sub_one_bound t) (by norm_num) (Or.inr (by norm_num)))
  source' := by
    apply ULift.down_injective
    apply Subtype.ext
    funext i
    fin_cases i <;> norm_num [classicalCellSquareBottomLeft, classicalCellSquareVertex]
  target' := by
    apply ULift.down_injective
    apply Subtype.ext
    funext i
    fin_cases i <;> norm_num [classicalCellSquareBottomRight, classicalCellSquareVertex]

/-- The bottom path has the actual two original coordinates. -/
theorem classicalCellSquareBottomPath_apply (t : I) :
    (classicalCellSquareBottomPath.{u} t).down.val = ![2 * (t : ℝ) - 1, -1] := rfl

/-- The right edge of the original square, traversed from bottom to top. -/
def classicalCellSquareRightPath :
    Path classicalCellSquareBottomRight.{u} classicalCellSquareTopRight.{u} where
  toFun t := ULift.up ⟨![1, 2 * (t : ℝ) - 1], by
    exact classicalCellSquare_mem_of_bounds _ _ (by norm_num)
      (classicalCellSquare_twice_sub_one_bound t) (Or.inl (by norm_num))⟩
  continuous_toFun := by
    exact continuous_classicalCellSquare_point (fun _ => 1) (fun t => 2 * (t : ℝ) - 1)
      continuous_const ((continuous_const.mul continuous_subtype_val).sub continuous_const)
      (fun t => classicalCellSquare_mem_of_bounds _ _ (by norm_num)
        (classicalCellSquare_twice_sub_one_bound t) (Or.inl (by norm_num)))
  source' := by
    apply ULift.down_injective
    apply Subtype.ext
    funext i
    fin_cases i <;> norm_num [classicalCellSquareBottomRight, classicalCellSquareVertex]
  target' := by
    apply ULift.down_injective
    apply Subtype.ext
    funext i
    fin_cases i <;> norm_num [classicalCellSquareTopRight, classicalCellSquareVertex]

/-- The right path has the actual two original coordinates. -/
theorem classicalCellSquareRightPath_apply (t : I) :
    (classicalCellSquareRightPath.{u} t).down.val = ![1, 2 * (t : ℝ) - 1] := rfl

/-- The top edge of the original square, traversed from right to left. -/
def classicalCellSquareTopPath :
    Path classicalCellSquareTopRight.{u} classicalCellSquareTopLeft.{u} where
  toFun t := ULift.up ⟨![1 - 2 * (t : ℝ), 1], by
    exact classicalCellSquare_mem_of_bounds _ _
      (classicalCellSquare_one_sub_twice_bound t) (by norm_num) (Or.inr (by norm_num))⟩
  continuous_toFun := by
    exact continuous_classicalCellSquare_point (fun t => 1 - 2 * (t : ℝ)) (fun _ => 1)
      (continuous_const.sub (continuous_const.mul continuous_subtype_val)) continuous_const
      (fun t => classicalCellSquare_mem_of_bounds _ _
        (classicalCellSquare_one_sub_twice_bound t) (by norm_num) (Or.inr (by norm_num)))
  source' := by
    apply ULift.down_injective
    apply Subtype.ext
    funext i
    fin_cases i <;> norm_num [classicalCellSquareTopRight, classicalCellSquareVertex]
  target' := by
    apply ULift.down_injective
    apply Subtype.ext
    funext i
    fin_cases i <;> norm_num [classicalCellSquareTopLeft, classicalCellSquareVertex]

/-- The top path has the actual two original coordinates. -/
theorem classicalCellSquareTopPath_apply (t : I) :
    (classicalCellSquareTopPath.{u} t).down.val = ![1 - 2 * (t : ℝ), 1] := rfl

/-- The left edge of the original square, traversed from top to bottom. -/
def classicalCellSquareLeftPath :
    Path classicalCellSquareTopLeft.{u} classicalCellSquareBottomLeft.{u} where
  toFun t := ULift.up ⟨![-1, 1 - 2 * (t : ℝ)], by
    exact classicalCellSquare_mem_of_bounds _ _ (by norm_num)
      (classicalCellSquare_one_sub_twice_bound t) (Or.inl (by norm_num))⟩
  continuous_toFun := by
    exact continuous_classicalCellSquare_point (fun _ => -1) (fun t => 1 - 2 * (t : ℝ))
      continuous_const (continuous_const.sub (continuous_const.mul continuous_subtype_val))
      (fun t => classicalCellSquare_mem_of_bounds _ _ (by norm_num)
        (classicalCellSquare_one_sub_twice_bound t) (Or.inl (by norm_num)))
  source' := by
    apply ULift.down_injective
    apply Subtype.ext
    funext i
    fin_cases i <;> norm_num [classicalCellSquareTopLeft, classicalCellSquareVertex]
  target' := by
    apply ULift.down_injective
    apply Subtype.ext
    funext i
    fin_cases i <;> norm_num [classicalCellSquareBottomLeft, classicalCellSquareVertex]

/-- The left path has the actual two original coordinates. -/
theorem classicalCellSquareLeftPath_apply (t : I) :
    (classicalCellSquareLeftPath.{u} t).down.val = ![-1, 1 - 2 * (t : ℝ)] := rfl

/-- The original square perimeter, starting at the bottom left corner and
traversing the bottom, right, top and left edges in that order. -/
def classicalCellSquarePerimeter :
    Path classicalCellSquareBottomLeft.{u} classicalCellSquareBottomLeft.{u} :=
  (classicalCellSquareBottomPath.trans classicalCellSquareRightPath).trans
    (classicalCellSquareTopPath.trans classicalCellSquareLeftPath)

variable {X : Type v} [TopologicalSpace X] {x : X}

/-- The actual mapped bottom path, with its endpoint casts, is the original based loop. -/
theorem classicalCellSquareLoopMap_bottomPath (η : Path x x) :
    ((classicalCellSquareBottomPath.{u}).map (classicalCellSquareLoopMap η).continuous).cast
        (classicalCellSquareLoopMap_bottomLeft η).symm
        (classicalCellSquareLoopMap_bottomRight η).symm = η := by
  apply Path.ext
  funext t
  change classicalCellSquareLoopMap η (classicalCellSquareBottomPath.{u} t) = η t
  have hb : classicalCellSquareBottomPath.{u} t ∈ classicalCellSquareBottom.{u} := rfl
  rw [classicalCellSquareLoopMap_bottom η _ hb]
  have hp : classicalCellSquareParameter (classicalCellSquareBottomPath.{u} t) = t := by
    apply Subtype.ext
    change (2 * (t : ℝ) - 1 + 1) / 2 = (t : ℝ)
    ring
  exact congrArg (fun s : I => η s) hp

/-- The actual mapped right path, with its endpoint casts, is constant at the basepoint. -/
theorem classicalCellSquareLoopMap_rightPath (η : Path x x) :
    ((classicalCellSquareRightPath.{u}).map (classicalCellSquareLoopMap η).continuous).cast
        (classicalCellSquareLoopMap_bottomRight η).symm
        (classicalCellSquareLoopMap_topRight η).symm = Path.refl x := by
  apply Path.ext
  funext t
  change classicalCellSquareLoopMap η (classicalCellSquareRightPath.{u} t) = x
  exact classicalCellSquareLoopMap_other η _ (Or.inr (Or.inl rfl))

/-- The actual mapped top path, with its endpoint casts, is constant at the basepoint. -/
theorem classicalCellSquareLoopMap_topPath (η : Path x x) :
    ((classicalCellSquareTopPath.{u}).map (classicalCellSquareLoopMap η).continuous).cast
        (classicalCellSquareLoopMap_topRight η).symm
        (classicalCellSquareLoopMap_topLeft η).symm = Path.refl x := by
  apply Path.ext
  funext t
  change classicalCellSquareLoopMap η (classicalCellSquareTopPath.{u} t) = x
  exact classicalCellSquareLoopMap_other η _ (Or.inr (Or.inr rfl))

/-- The actual mapped left path, with its endpoint casts, is constant at the basepoint. -/
theorem classicalCellSquareLoopMap_leftPath (η : Path x x) :
    ((classicalCellSquareLeftPath.{u}).map (classicalCellSquareLoopMap η).continuous).cast
        (classicalCellSquareLoopMap_topLeft η).symm
        (classicalCellSquareLoopMap_bottomLeft η).symm = Path.refl x := by
  apply Path.ext
  funext t
  change classicalCellSquareLoopMap η (classicalCellSquareLeftPath.{u} t) = x
  exact classicalCellSquareLoopMap_other η _ (Or.inl rfl)

/-- The original based fundamental-group map sends the actual perimeter class to the
original loop class. -/
theorem classicalCellSquareLoopMap_perimeter (η : Path x x) :
    FundamentalGroup.mapOfEq (classicalCellSquareLoopMap η)
        (classicalCellSquareLoopMap_bottomLeft η)
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk classicalCellSquarePerimeter.{u})) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk η) := by
  let f : C(classicalCellSquareBoundary.{u}, X) := classicalCellSquareLoopMap η
  have hb : f classicalCellSquareBottomLeft.{u} = x :=
    classicalCellSquareLoopMap_bottomLeft η
  have hr : f classicalCellSquareBottomRight.{u} = x :=
    classicalCellSquareLoopMap_bottomRight η
  have ht : f classicalCellSquareTopRight.{u} = x :=
    classicalCellSquareLoopMap_topRight η
  have hl : f classicalCellSquareTopLeft.{u} = x :=
    classicalCellSquareLoopMap_topLeft η
  have hp : (classicalCellSquarePerimeter.{u}.map f.continuous).cast hb.symm hb.symm =
      (η.trans (Path.refl x)).trans ((Path.refl x).trans (Path.refl x)) := by
    unfold classicalCellSquarePerimeter
    simp only [Path.map_trans]
    rw [Path.cast_trans _ _ hb.symm ht.symm hb.symm]
    rw [Path.cast_trans _ _ hb.symm hr.symm ht.symm,
      Path.cast_trans _ _ ht.symm hl.symm hb.symm]
    simp only [classicalCellSquareLoopMap_bottomPath η, classicalCellSquareLoopMap_rightPath η,
      classicalCellSquareLoopMap_topPath η, classicalCellSquareLoopMap_leftPath η]
  apply CategoryTheory.End.ext
  rw [FundamentalGroup.mapOfEq_apply]
  change ((Path.Homotopic.Quotient.mk classicalCellSquarePerimeter.{u}).map f).cast
      hb.symm hb.symm = Path.Homotopic.Quotient.mk η
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast, hp]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_refl,
    Path.Homotopic.Quotient.trans_refl]

end Topology.CWComplex
