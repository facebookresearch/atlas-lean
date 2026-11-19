/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Numerical.PhysicalGalerkinError
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Numerical.PhysicalGalerkinError`

* the nonunit bar `EA = 2`, `L = 3`, `q = 4`: stiffness `8 / 3`, load `6`, interior coefficient
  `9 / 4`; the approximate coefficient `2` leaves the residual `2 / 3`, and its coefficient error
  `1 / 4` attains the residual bound;
* the same bar and coefficient: the displacement error at the interior node, its energy and its
  squared `L²` norm carry the three different reconstruction factors `1`, `K` and `L / 3`;
* zero rigidity, where Lean's `x / 0 = 0` makes the residual bound vanish;
* the quadratic load `Q * (x / L) ^ 2` on the same bar with `Q = 4`: amplitude `18`,
  exact-load coefficient `21 / 32`, midpoint-quadrature coefficient `45 / 64`, difference
  `3 / 64`.
-/

@[expose] public section

namespace PhyslibExtTest.Numerical.PhysicalGalerkinError

open _root_.PhysicalGalerkinError PhysicalErrorBudgets MathlibExt.Analysis.ODE.FiniteElement1D

/-! ## A. A nonunit bar with an approximate coefficient -/

/-- Nonzero residual on the nonunit bar `EA = 2`, `L = 3`, `q = 4`: `K = 8 / 3`, `F = 6` and
`c = 9 / 4`. The approximate coefficient `2` leaves the residual `2 / 3`, and its coefficient error
`1 / 4` equals the bound `3 * |2 / 3| / (4 * 2)`. -/
example :
    twoCellStiffness 2 3 = 8 / 3 ∧ twoCellLoad 3 4 = 6 ∧ twoCellCoeff 2 3 4 = 9 / 4 ∧
      twoCellResidual 2 3 4 2 = 2 / 3 ∧ |twoCellCoeff 2 3 4 - 2| = 1 / 4 ∧
      3 * |twoCellResidual 2 3 4 2| / (4 * 2) = 1 / 4 := by
  have hc : twoCellCoeff 2 3 4 = 9 / 4 := by
    rw [twoCellCoeff_eq (by norm_num)]
    norm_num
  refine ⟨by norm_num [twoCellStiffness], by norm_num [twoCellLoad], hc, ?_, ?_, ?_⟩
  · norm_num [twoCellResidual, twoCellStiffness, twoCellLoad]
  · rw [hc]
    norm_num [abs_of_pos]
  · norm_num [twoCellResidual, twoCellStiffness, twoCellLoad, abs_of_pos]

/-- The three reconstruction factors on the same bar and coefficient: the displacement error at
the interior node is the coefficient error `1 / 4` (factor `1`), the energy is
`1 / 6 = (8 / 3) * (1 / 4) ^ 2` (factor `K`), and the squared `L²` norm is
`1 / 16 = (3 / 3) * (1 / 4) ^ 2` (factor `L / 3`); the energy is not the squared coefficient
error. -/
example :
    physicalP1 twoCells 2 3 4 (3 / 2) - twoCellReconstruction 3 2 (3 / 2) = 1 / 4 ∧
      ∫ x in (0 : ℝ)..3,
          2 * deriv (fun x => physicalP1 twoCells 2 3 4 x - twoCellReconstruction 3 2 x) x ^ 2 =
        1 / 6 ∧
      ∫ x in (0 : ℝ)..3, (physicalP1 twoCells 2 3 4 x - twoCellReconstruction 3 2 x) ^ 2 =
        1 / 16 ∧
      (1 / 6 : ℝ) ≠ (1 / 4) ^ 2 := by
  have hc : twoCellCoeff 2 3 4 = 9 / 4 := by
    rw [twoCellCoeff_eq (by norm_num)]
    norm_num
  have hhat : hat twoCells 1 (1 / 2) = 1 :=
    (p1_points twoCells (Pi.single 1 1 : Fin (twoCells.n + 1) → ℝ) 1).trans (Pi.single_eq_same _ _)
  obtain ⟨hE1, -⟩ := integral_energy_reconstruction_error (EA := 2) (L := 3) (by norm_num)
    (by norm_num) 4 2
  refine ⟨?_, ?_, ?_, by norm_num⟩
  · rw [physicalP1_sub_twoCellReconstruction (by norm_num), hc,
      show (3 / 2 : ℝ) / 3 = 1 / 2 by norm_num, hhat]
    norm_num
  · rw [hE1, hc]
    norm_num [twoCellStiffness]
  · rw [integral_sq_reconstruction_error (by norm_num), hc]
    norm_num

/-- Zero rigidity is excluded: at `EA = 0`, Lean's `x / 0 = 0` makes the bound
`L * |r| / (4 * EA)` vanish, while the coefficient error of `c̃ = 1` on `L = 3`, `q = 4` is
`1`. -/
example :
    |twoCellCoeff 0 3 4 - 1| = 1 ∧ 3 * |twoCellResidual 0 3 4 1| / (4 * 0) = 0 := by
  have hc : twoCellCoeff 0 3 4 = 0 := by
    rw [twoCellCoeff_eq (by norm_num)]
    norm_num
  refine ⟨?_, by norm_num⟩
  rw [hc]
  norm_num

/-! ## B. The quadratic load on the same bar -/

/-- Nonunit fixture `EA = 2`, `L = 3`, `Q = 4`: `β = 18`, exact coefficient `21 / 32`, midpoint
coefficient `45 / 64`, difference `3 / 64`. -/
example :
    quadAmplitude 2 3 4 = 18 ∧ quadCoeff 2 3 4 = 21 / 32 ∧ quadMidpointCoeff 2 3 4 = 45 / 64 ∧
      quadMidpointCoeff 2 3 4 - quadCoeff 2 3 4 = 3 / 64 := by
  have hβ : quadAmplitude 2 3 4 = 18 := by norm_num [quadAmplitude]
  have hc := (quadCoeff_eq (EA := 2) (L := 3) (by norm_num) (by norm_num) 4).1
  have hm := quadMidpointCoeff_eq (EA := 2) (L := 3) (by norm_num) (by norm_num) 4
  rw [hβ] at hc hm
  refine ⟨hβ, by rw [hc]; norm_num, by rw [hm]; norm_num, by rw [hc, hm]; norm_num⟩

end PhyslibExtTest.Numerical.PhysicalGalerkinError

end
