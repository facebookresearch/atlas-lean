/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.HodgkinHuxleyCurrent

/-! Tests for the Hodgkin–Huxley equilibrium branch with applied current. All checks below are
computed from the definitions (explicit eigenvectors, direct evaluation of quartics and of the
vector field), not through the theorems they exercise:

* the branch at `I = 0` is T199's resting state, and `I∞(0) = 0`;
* a branch point is an equilibrium for its own current (`V = 15` mV, evaluated directly);
* an arrowhead matrix meeting the hypotheses of `Arrow.isHopf_of_hdet_eq_zero` exists and has the
  eigenvalue `i` with an explicit eigenvector (non-vacuity of the Hopf alternative);
* an arrowhead matrix with `coef₄ = 0` has the eigenvalue `0` (non-vacuity of the fold
  alternative);
* a quartic with all coefficients positive but `Δ₃ < 0` has the root `1 + 2 i` (boundary: the
  Routh–Hurwitz hypothesis `Δ₃ > 0` cannot be dropped). -/

open Real Set

namespace MathlibExtTest.Biology.Biophysics.HodgkinHuxleyCurrent

open MathlibExt.Biology.Biophysics.HodgkinHuxley
open MathlibExt.Biology.Biophysics.HodgkinHuxleyCurrent

/-! ### The branch at `I = 0` -/

example : eqPoint 0 = rest := rfl
example : squidI 0 = squid := rfl

/-- `I∞(0) = 0`, by unfolding the leak reversal potential. -/
example : Iss 0 = 0 := by
  simp only [Iss, ionic, squid, squidEL, mInf, hInf, nInf, mRest, hRest, nRest]
  ring

/-- The branch point at `V = 15` mV is an equilibrium for the current `I∞(15)`, evaluated
component by component from `field`. -/
example : field (squidI (Iss 15)) (eqPoint 15) = 0 := by
  have hm := add_pos (alphaM_pos 15) (betaM_pos 15)
  have hh := add_pos (alphaH_pos 15) (betaH_pos 15)
  have hn := add_pos (alphaN_pos 15) (betaN_pos 15)
  funext i
  fin_cases i
  · simp [field, eqPoint, squidI, Iss, squid, ionic]
  · simp only [field, eqPoint, gate, mInf, steady]
    simp
    field_simp
    ring
  · simp only [field, eqPoint, gate, hInf, steady]
    simp
    field_simp
    ring
  · simp only [field, eqPoint, gate, nInf, steady]
    simp
    field_simp
    ring

/-! ### Non-vacuity of the Hopf alternative -/

/-- `[[1, 1, 0, 0], [-2, -1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -2]]`: the upper block has
eigenvalues `± i`. -/
def hopfExample : Arrow :=
  { a := 1, b₁ := 1, b₂ := 0, b₃ := 0, c₁ := -2, c₂ := 0, c₃ := 0, k₁ := 1, k₂ := 1, k₃ := 2 }

example : hopfExample.coef₁ = 3 ∧ hopfExample.coef₂ = 3 ∧ hopfExample.coef₃ = 3 ∧
    hopfExample.coef₄ = 2 ∧ hopfExample.hdet = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [hopfExample, Arrow.coef₁, Arrow.coef₂, Arrow.coef₃, Arrow.coef₄, Arrow.hdet,
      hurwitz3]

/-- `i` is an eigenvalue: `M v = i v` for `v = (1, i - 1, 0, 0)`, computed entrywise. -/
example : (hopfExample.mat.map (algebraMap ℝ ℂ)).mulVec ![1, Complex.I - 1, 0, 0] =
    Complex.I • ![1, Complex.I - 1, 0, 0] := by
  funext i
  fin_cases i <;> simp [hopfExample, Arrow.mat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  linear_combination -Complex.I_sq

/-! ### Non-vacuity of the fold alternative -/

/-- `[[0, 0, 0, 0], [0, -1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]]` has `coef₄ = 0`. -/
def foldExample : Arrow :=
  { a := 0, b₁ := 0, b₂ := 0, b₃ := 0, c₁ := 0, c₂ := 0, c₃ := 0, k₁ := 1, k₂ := 1, k₃ := 1 }

example : foldExample.coef₄ = 0 := by norm_num [foldExample, Arrow.coef₄]

example : (foldExample.mat.map (algebraMap ℝ ℂ)).mulVec ![1, 0, 0, 0] = 0 := by
  funext i
  fin_cases i <;> simp [foldExample, Arrow.mat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-! ### Boundary: Routh–Hurwitz needs `Δ₃ > 0` -/

/-- `μ⁴ + μ³ + μ² + 11 μ + 10 = (μ² - 2 μ + 5)(μ² + 3 μ + 2)`: all coefficients positive. -/
example : hurwitz3 1 1 11 10 < 0 := by norm_num [hurwitz3]

/-- …and the root `1 + 2 i` lies in the right half-plane. -/
example : quartic 1 1 11 10 (1 + 2 * Complex.I) = 0 ∧ 0 < (1 + 2 * Complex.I).re := by
  refine ⟨?_, by simp⟩
  simp only [quartic]
  push_cast
  linear_combination (16 * Complex.I ^ 2 + 40 * Complex.I + 24) * Complex.I_sq

end MathlibExtTest.Biology.Biophysics.HodgkinHuxleyCurrent
