/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Euclidean.ApollonianDescartesQuadruples

/-!
# Tests for Descartes quadruples and the Apollonian group
-/

namespace MathlibExtTest.Geometry.Euclidean.ApollonianDescartesQuadruples

open MathlibExt.Geometry.Euclidean.ApollonianDescartesQuadruples

/-- The bounded packing of Figure 3 in Lagarias–Mallows–Wilks: `(-1, 2, 2, 3)` is a Descartes
quadruple. -/
example : descartesForm (![-1, 2, 2, 3] : Fin 4 → ℤ) = 0 := by
  simp [descartesForm, Fin.sum_univ_four]

/-- Flipping the bounding circle of `(-1, 2, 2, 3)` gives the circle of curvature `15`. -/
example : apollonianFlip 0 (![-1, 2, 2, 3] : Fin 4 → ℤ) = ![15, 2, 2, 3] := by
  decide

/-- Flipping the last circle of `(-1, 2, 2, 3)` gives the other circle of curvature `3`
(the configuration is symmetric). -/
example : apollonianFlip 3 (![-1, 2, 2, 3] : Fin 4 → ℤ) = ![-1, 2, 2, 3] := by
  decide

/-- Zero curvature (a line) is allowed: the strip packing `(0, 0, 1, 1)` between two parallel
lines is a Descartes quadruple and flipping a line gives the circle of curvature `4`. -/
example : descartesForm (![0, 0, 1, 1] : Fin 4 → ℝ) = 0 := by
  simp [descartesForm, Fin.sum_univ_four]; norm_num

example : apollonianFlip 0 (![0, 0, 1, 1] : Fin 4 → ℤ) = ![4, 0, 1, 1] := by
  decide

/-- A real quadruple obtained by two flips from an integral Descartes quadruple is a Descartes
quadruple with integer entries. -/
example : (![15, 2, 2, 35] : Fin 4 → ℝ) ∈ apollonianOrbit (![-1, 2, 2, 3] : Fin 4 → ℝ) := by
  refine ⟨[3, 0], ?_⟩
  funext j
  fin_cases j <;> simp [apollonianFlip, Fin.sum_univ_four, Function.update] <;> norm_num

example (w : Fin 4 → ℝ) (hw : w ∈ apollonianOrbit (![-1, 2, 2, 3] : Fin 4 → ℝ)) :
    descartesForm w = 0 ∧ IsIntegralQuadruple w := by
  refine ⟨?_, ?_⟩
  · rw [descartesForm_of_mem_apollonianOrbit hw]
    simp [descartesForm, Fin.sum_univ_four]; norm_num
  · refine IsIntegralQuadruple.of_mem_apollonianOrbit ?_ hw
    intro i
    fin_cases i
    · exact ⟨-1, by simp⟩
    · exact ⟨2, by simp⟩
    · exact ⟨2, by simp⟩
    · exact ⟨3, by simp⟩

/-- The two roots of the Descartes relation for `(-1, 2, 2, ·)` are `3` and `3`; for
`(-1, 2, 3, ·)` they are `6` and `2`: any `x` completing `(-1, 2, 3, x)` to a Descartes quadruple
is one of these. -/
example (x : ℚ) (hx : descartesForm (Function.update (![-1, 2, 3, 6] : Fin 4 → ℚ) 3 x) = 0) :
    x = 6 ∨ x = 2 := by
  have h := eq_or_eq_flip_of_descartesForm_update_eq_zero
    (v := (![-1, 2, 3, 6] : Fin 4 → ℚ)) (i := 3)
    (by simp [descartesForm, Fin.sum_univ_four]; norm_num) hx
  simp [Fin.sum_univ_four] at h
  norm_num at h
  exact h

/-- The flip `S₁` is a reflection: it is an involution and negates `e₁`. -/
example (v : Fin 4 → ℤ) : apollonianFlip 0 (apollonianFlip 0 v) = v :=
  apollonianFlip_apollonianFlip 0 v

example : apollonianFlip 1 (Pi.single 1 (1 : ℤ)) = -Pi.single 1 1 :=
  apollonianFlip_single 1

end MathlibExtTest.Geometry.Euclidean.ApollonianDescartesQuadruples
