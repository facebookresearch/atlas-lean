/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.Normed.Module.QuotientSeminorm
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.NormNum

/-!
# The quotient seminorm of a real plane by a line

Use the actual product norm on `ℝ × ℝ` and quotient by the vertical line.
The induced seminorm of the class of `(x,y)` is `|x|`. In particular `(3,4)`
has quotient seminorm three and nonzero class, while `(0,7)` has zero class.
The actual quotient topology satisfies the finite-supremum `WithSeminorms` theorem.
-/

noncomputable section
open Set

namespace QuotientPlaneConcreteSmoke

private abbrev Plane := ℝ × ℝ
private def p : Seminorm ℝ Plane := normSeminorm ℝ Plane
private def vertical : Submodule ℝ Plane := (LinearMap.fst ℝ ℝ ℝ).ker

private theorem quotient_value (x y : ℝ) :
    p.quotient vertical (vertical.mkQ (x, y)) = |x| := by
  rw [Seminorm.quotient_mkQ]
  let q : vertical → ℝ := fun v => p ((x, y) + (v : Plane))
  have hb : BddBelow (Set.range q) := by
    refine ⟨0, ?_⟩
    rintro v ⟨w, rfl⟩
    change 0 ≤ ‖(x, y) + (w : Plane)‖
    exact norm_nonneg _
  let cancel : vertical := ⟨(0, -y), by change (0 : ℝ) = 0; rfl⟩
  have hcancel : q cancel = |x| := by
    change ‖(x, y) + ((0, -y) : Plane)‖ = |x|
    have hv : (x, y) + ((0, -y) : Plane) = (x, 0) := by ext <;> simp
    rw [hv, Prod.norm_mk, norm_zero, Real.norm_eq_abs, max_eq_left (abs_nonneg x)]
  apply le_antisymm
  · exact (csInf_le hb (Set.mem_range_self cancel)).trans hcancel.le
  · apply le_csInf (show (Set.range q).Nonempty from ⟨q 0, ⟨0, rfl⟩⟩)
    rintro v ⟨w, rfl⟩
    have hw := w.property
    change (w : Plane).1 = 0 at hw
    have hfst : ((x, y) + (w : Plane)).1 = x := by simp [hw]
    calc
      |x| = ‖((x, y) + (w : Plane)).1‖ := by rw [hfst, Real.norm_eq_abs]
      _ ≤ ‖(x, y) + (w : Plane)‖ := norm_fst_le _
      _ = q w := rfl

example : p.quotient vertical (vertical.mkQ (3, 4)) = 3 := by
  rw [quotient_value]
  norm_num

example : vertical.mkQ (3, 4) ≠ 0 := by
  intro hzero
  have h := congrArg (p.quotient vertical) hzero
  rw [quotient_value] at h
  simp only [map_zero] at h
  norm_num at h

example : vertical.mkQ (0, 7) = 0 := by
  have hk : ((0, 7) : Plane) ∈ LinearMap.ker vertical.mkQ := by
    rw [Submodule.ker_mkQ]
    change (0 : ℝ) = 0
    rfl
  exact LinearMap.mem_ker.mp hk

example : WithSeminorms
    (fun s : Finset Unit => (s.sup (fun _ : Unit => p)).quotient vertical) := by
  exact (norm_withSeminorms ℝ Plane).quotient vertical

end QuotientPlaneConcreteSmoke
