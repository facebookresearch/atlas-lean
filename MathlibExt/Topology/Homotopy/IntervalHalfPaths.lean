/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Subpath
public meta import Mathlib.Tactic.Linarith
public meta import Mathlib.Tactic.Ring

/-!
# Actual interval half paths and their original concatenation maps

The two affine half paths concatenate to the literal identity interval
path. Mapping them through an original concatenated path recovers both
original legs with the derived source, joining-point and target casts.
The right half's zero-time joining case is included.
-/

public section

noncomputable section

open unitInterval
open scoped Topology

universe u

namespace unitInterval

/-- The literal midpoint used by the original concatenation half rule. -/
def pathHalfPoint : I := ⟨1 / 2, by constructor <;> norm_num⟩

private theorem originalPathHalfPointValueComputed : (pathHalfPoint : ℝ) = 1 / 2 := rfl

/-- The actual real value of the original interval joining point. -/
theorem pathHalfPoint_coe : (pathHalfPoint : ℝ) = 1 / 2 :=
  originalPathHalfPointValueComputed

/-- The actual affine first half of the original interval. -/
def pathHalfLeft : Path (0 : I) pathHalfPoint :=
  Path.id.subpath 0 pathHalfPoint

/-- The affine second half is the corresponding subpath of the identity. -/
def pathHalfRight : Path pathHalfPoint (1 : I) :=
  Path.id.subpath pathHalfPoint 1

private theorem originalPathHalfLeftSubpathComputed :
    pathHalfLeft = Path.id.subpath 0 pathHalfPoint := rfl

private theorem originalPathHalfRightSubpathComputed :
    pathHalfRight = Path.id.subpath pathHalfPoint 1 := rfl

/-- The first-half alias uses Mathlib's original subpath API. -/
theorem pathHalfLeft_eq_subpath : pathHalfLeft = Path.id.subpath 0 pathHalfPoint :=
  originalPathHalfLeftSubpathComputed

/-- The second-half alias uses Mathlib's original subpath API. -/
theorem pathHalfRight_eq_subpath : pathHalfRight = Path.id.subpath pathHalfPoint 1 :=
  originalPathHalfRightSubpathComputed

private theorem originalPathHalfLeftValueComputed (s : I) :
    (pathHalfLeft s : ℝ) = (s : ℝ) / 2 := by
  change (1 - (s : ℝ)) * 0 + (s : ℝ) * (pathHalfPoint : ℝ) = (s : ℝ) / 2
  rw [pathHalfPoint_coe]
  ring

private theorem originalPathHalfRightValueComputed (s : I) :
    (pathHalfRight s : ℝ) = (1 + (s : ℝ)) / 2 := by
  change (1 - (s : ℝ)) * (pathHalfPoint : ℝ) + (s : ℝ) * 1 = (1 + (s : ℝ)) / 2
  rw [pathHalfPoint_coe]
  ring

/-- Every actual first-half parameter has its exact affine value. -/
theorem pathHalfLeft_coe (s : I) : (pathHalfLeft s : ℝ) = (s : ℝ) / 2 :=
  originalPathHalfLeftValueComputed s

/-- Every actual second-half parameter has its exact affine value. -/
theorem pathHalfRight_coe (s : I) : (pathHalfRight s : ℝ) = (1 + (s : ℝ)) / 2 :=
  originalPathHalfRightValueComputed s

private theorem originalPathHalfConcatenationComputed :
    pathHalfLeft.trans pathHalfRight = Path.id := by
  apply Path.ext
  funext s
  have h := Path.trans_apply pathHalfLeft pathHalfRight s
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · let r : I := ⟨2 * (s : ℝ),
      (mul_pos_mem_iff zero_lt_two).2 ⟨unitInterval.nonneg s, hs⟩⟩
    have hValue : (pathHalfLeft.trans pathHalfRight) s = pathHalfLeft r :=
      h.trans (dite_eq_left hs)
    have hParam : pathHalfLeft r = s := by
      apply Subtype.ext
      rw [pathHalfLeft_coe]
      change 2 * (s : ℝ) / 2 = (s : ℝ)
      ring
    exact hValue.trans hParam
  · let r : I := ⟨2 * (s : ℝ) - 1,
      two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, unitInterval.le_one s⟩⟩
    have hValue : (pathHalfLeft.trans pathHalfRight) s = pathHalfRight r :=
      h.trans (dite_eq_right hs)
    have hParam : pathHalfRight r = s := by
      apply Subtype.ext
      rw [pathHalfRight_coe]
      change (1 + (2 * (s : ℝ) - 1)) / 2 = (s : ℝ)
      ring
    exact hValue.trans hParam

/-- The whole two actual half paths concatenate to the original
identity interval path, with the original half clocks. -/
theorem pathHalfLeft_trans_right : pathHalfLeft.trans pathHalfRight = Path.id :=
  originalPathHalfConcatenationComputed

end unitInterval

namespace Path

variable {Y : Type u} [TopologicalSpace Y] {a b c : Y}

private theorem originalTransHalfPointComputed (p : Path a b) (q : Path b c) :
    (p.trans q) unitInterval.pathHalfPoint = b := by
  have hm : (unitInterval.pathHalfPoint : ℝ) ≤ 1 / 2 :=
    le_of_eq unitInterval.pathHalfPoint_coe
  let r : I := ⟨2 * (unitInterval.pathHalfPoint : ℝ),
    (mul_pos_mem_iff zero_lt_two).2 ⟨unitInterval.nonneg unitInterval.pathHalfPoint, hm⟩⟩
  have hValue : (p.trans q) unitInterval.pathHalfPoint = p r :=
    (Path.trans_apply p q unitInterval.pathHalfPoint).trans (dite_eq_left hm)
  have hParam : r = 1 := by
    apply Subtype.ext
    change 2 * (unitInterval.pathHalfPoint : ℝ) = 1
    rw [unitInterval.pathHalfPoint_coe]
    norm_num
  exact hValue.trans ((congrArg p hParam).trans p.target)

/-- The actual original concatenated path has its exact joining point
at the literal interval midpoint. -/
theorem trans_pathHalfPoint (p : Path a b) (q : Path b c) :
    (p.trans q) unitInterval.pathHalfPoint = b :=
  originalTransHalfPointComputed p q

private theorem originalIntervalHalfLeftMapComputed (p : Path a b) (q : Path b c) :
    (unitInterval.pathHalfLeft.map (p.trans q).continuous).cast
      (x' := a) (y' := b) (p.trans q).source.symm (trans_pathHalfPoint p q).symm = p := by
  apply Path.ext
  funext s
  change (p.trans q) (unitInterval.pathHalfLeft s) = p s
  have hs : (unitInterval.pathHalfLeft s : ℝ) ≤ 1 / 2 := by
    rw [unitInterval.pathHalfLeft_coe]
    linarith [unitInterval.le_one s]
  let r : I := ⟨2 * (unitInterval.pathHalfLeft s : ℝ),
    (mul_pos_mem_iff zero_lt_two).2 ⟨unitInterval.nonneg (unitInterval.pathHalfLeft s), hs⟩⟩
  have hValue : (p.trans q) (unitInterval.pathHalfLeft s) = p r :=
    (Path.trans_apply p q (unitInterval.pathHalfLeft s)).trans (dite_eq_left hs)
  have hParam : r = s := by
    apply Subtype.ext
    change 2 * (unitInterval.pathHalfLeft s : ℝ) = (s : ℝ)
    rw [unitInterval.pathHalfLeft_coe]
    ring
  exact hValue.trans (congrArg p hParam)

/-- Mapping the actual first half through the same original
concatenation recovers the whole first root with derived endpoint casts. -/
theorem intervalHalfLeft_map_trans (p : Path a b) (q : Path b c) :
    (unitInterval.pathHalfLeft.map (p.trans q).continuous).cast
      (x' := a) (y' := b) (p.trans q).source.symm (trans_pathHalfPoint p q).symm = p :=
  originalIntervalHalfLeftMapComputed p q

private theorem originalIntervalHalfRightMapComputed (p : Path a b) (q : Path b c) :
    (unitInterval.pathHalfRight.map (p.trans q).continuous).cast
      (x' := b) (y' := c) (trans_pathHalfPoint p q).symm (p.trans q).target.symm = q := by
  apply Path.ext
  funext s
  change (p.trans q) (unitInterval.pathHalfRight s) = q s
  by_cases hsZero : s = 0
  · subst s
    exact (congrArg (p.trans q) unitInterval.pathHalfRight.source).trans
      ((trans_pathHalfPoint p q).trans q.source.symm)
  · have hsNonzero : (s : ℝ) ≠ 0 := by
      intro h
      apply hsZero
      exact Subtype.ext h
    have hsPositive : 0 < (s : ℝ) :=
      lt_of_le_of_ne (unitInterval.nonneg s) hsNonzero.symm
    have hs : ¬(unitInterval.pathHalfRight s : ℝ) ≤ 1 / 2 := by
      rw [unitInterval.pathHalfRight_coe]
      linarith
    let r : I := ⟨2 * (unitInterval.pathHalfRight s : ℝ) - 1,
      two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le,
        unitInterval.le_one (unitInterval.pathHalfRight s)⟩⟩
    have hValue : (p.trans q) (unitInterval.pathHalfRight s) = q r :=
      (Path.trans_apply p q (unitInterval.pathHalfRight s)).trans (dite_eq_right hs)
    have hParam : r = s := by
      apply Subtype.ext
      change 2 * (unitInterval.pathHalfRight s : ℝ) - 1 = (s : ℝ)
      rw [unitInterval.pathHalfRight_coe]
      ring
    exact hValue.trans (congrArg q hParam)

/-- Mapping the actual second half through the same original
concatenation recovers the whole second root, including its zero-time join. -/
theorem intervalHalfRight_map_trans (p : Path a b) (q : Path b c) :
    (unitInterval.pathHalfRight.map (p.trans q).continuous).cast
      (x' := b) (y' := c) (trans_pathHalfPoint p q).symm (p.trans q).target.symm = q :=
  originalIntervalHalfRightMapComputed p q

end Path

end
