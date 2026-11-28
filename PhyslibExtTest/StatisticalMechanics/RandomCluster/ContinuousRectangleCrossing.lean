/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.ContinuousRectangleCrossing

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.ContinuousRectangleCrossing`

* `clampCoord` evaluates at points inside, below and above `[0, 1]`;
* `unitSquare_paths_intersect` on an explicit instance: the horizontal segment at height `1/2` and
  the vertical segment at abscissa `1/2` in `[0, 1]²` meet;
* `rectangle_paths_intersect` in conditional form on the rectangle `[0, 2] × [0, 1]`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.ContinuousRectangleCrossing

open _root_.StatMech _root_.StatMech.ContinuousRectangleCrossing

-- Clamping to `[0, 1]`.
example : clampCoord 0 1 (1 / 2) = 1 / 2 ∧ clampCoord 0 1 (-3) = 0 ∧ clampCoord 0 1 5 = 1 := by
  refine ⟨clampCoord_of_mem (by norm_num) (by norm_num),
    clampCoord_of_le_left (by norm_num) (by norm_num),
    clampCoord_of_right_le (by norm_num) (by norm_num)⟩

/-- The horizontal segment from `(0, 1/2)` to `(1, 1/2)`. -/
noncomputable def hseg : Path (![0, 1 / 2] : Fin 2 → ℝ) ![1, 1 / 2] where
  toFun t := ![(t : ℝ), 1 / 2]
  continuous_toFun := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_subtype_val
    · exact continuous_const
  source' := by simp
  target' := by simp

/-- The vertical segment from `(1/2, 0)` to `(1/2, 1)`. -/
noncomputable def vseg : Path (![1 / 2, 0] : Fin 2 → ℝ) ![1 / 2, 1] where
  toFun t := ![1 / 2, (t : ℝ)]
  continuous_toFun := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_const
    · exact continuous_subtype_val
  source' := by simp
  target' := by simp

/-- A point of the form `![a, b]` with `a, b ∈ [0, 1]` lies in the unit square. -/
theorem inUnitSquare_vec {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    InUnitSquare ![a, b] := by
  intro i
  fin_cases i
  · exact ha
  · exact hb

-- The two segments of the unit square meet.
example : ∃ t s : unitInterval, hseg t = vseg s :=
  unitSquare_paths_intersect hseg vseg
    (by
      rintro _ ⟨t, rfl⟩
      exact inUnitSquare_vec ⟨t.2.1, t.2.2⟩ (by norm_num))
    (by
      rintro _ ⟨t, rfl⟩
      exact inUnitSquare_vec (by norm_num) ⟨t.2.1, t.2.2⟩)
    (by simp) (by simp) (by simp) (by simp)

-- Left-right and bottom-top paths in `[0, 2] × [0, 1]` meet.
example {hl hr vb vt : Fin 2 → ℝ} (γ : Path hl hr) (η : Path vb vt)
    (hγ : Set.range γ ⊆ {x | InRectangle 0 2 0 1 x})
    (hη : Set.range η ⊆ {x | InRectangle 0 2 0 1 x})
    (hl0 : hl 0 = 0) (hr0 : hr 0 = 2) (vb1 : vb 1 = 0) (vt1 : vt 1 = 1) :
    ∃ t s : unitInterval, γ t = η s :=
  rectangle_paths_intersect (by norm_num) (by norm_num) γ η hγ hη hl0 hr0 vb1 vt1

end PhyslibExtTest.StatisticalMechanics.RandomCluster.ContinuousRectangleCrossing
