/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.PlanarStability

/-! Tests for `MathlibExt.Biology.Dynamics.PlanarStability` on concrete `2 × 2` matrices: a stable
node `diag(-1, -2)`, the center `!![0, -1; 1, 0]` (eigenvalues `± i`), and the saddle
`diag(1, -1)`, through the Hurwitz and instability criteria, the spectrum, and the classification;
and the polynomial forms on `z² + z + 1` and `z² - 3 z + 2`. -/

open Matrix MathlibExt.Biology.Dynamics.PlanarStability

namespace MathlibExtTest.Biology.Dynamics.PlanarStability

/-- `diag(-1, -2)`: trace `-3 < 0 < 2 = det`, so it is Hurwitz. -/
example : (!![-1, 0; 0, -2] : Matrix (Fin 2) (Fin 2) ℝ).IsHurwitz := by
  rw [isHurwitz_iff_trace_neg_and_det_pos]
  norm_num [Matrix.trace_fin_two, Matrix.det_fin_two]

/-- Its classification is a stable node (`4 Δ = 8 ≤ 9 = τ²`). -/
example : linearType (-3) 2 = .stableNode :=
  linearType_eq_stableNode_iff.2 ⟨by norm_num, by norm_num, by norm_num⟩

/-- `i` is an eigenvalue of the rotation generator `!![0, -1; 1, 0]` (trace `0`, determinant
`1`). -/
example : Complex.I ∈ spectrum ℂ ((!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ).map
    (algebraMap ℝ ℂ)) := by
  rw [mem_spectrum_iff_isCharRoot, IsCharRoot]
  simp [Matrix.trace_fin_two, Matrix.det_fin_two]

/-- The center is not Hurwitz: its eigenvalues lie on the imaginary axis. -/
example : ¬ (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ).IsHurwitz := by
  rw [isHurwitz_iff_trace_neg_and_det_pos]
  norm_num [Matrix.trace_fin_two]

/-- Nor does it have an eigenvalue with positive real part. -/
example : ¬ ∃ μ ∈ spectrum ℂ ((!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ).map (algebraMap ℝ ℂ)),
    0 < μ.re := by
  rw [exists_spectrum_re_pos_iff]
  norm_num [Matrix.trace_fin_two, Matrix.det_fin_two]

example : linearType 0 1 = .center := linearType_eq_center_iff.2 ⟨one_pos, rfl⟩

/-- The saddle `diag(1, -1)` (determinant `-1 < 0`) has an eigenvalue with positive real part. -/
example : ∃ μ ∈ spectrum ℂ ((!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ).map (algebraMap ℝ ℂ)),
    0 < μ.re :=
  (exists_spectrum_re_pos_iff _).2 (Or.inr (by norm_num [Matrix.det_fin_two]))

example : linearType 0 (-1) = .saddle := linearType_eq_saddle_iff.2 (by norm_num)

/-- Polynomial forms: `z² + z + 1` (`τ = -1`, `Δ = 1`) is stable, `z² - 3 z + 2` (roots `1`, `2`)
is unstable, with `2` as a root. -/
example : IsLinearlyStable (-1) 1 := isLinearlyStable_iff.2 ⟨by norm_num, by norm_num⟩

example : IsLinearlyUnstable 3 2 := isLinearlyUnstable_iff.2 (Or.inl (by norm_num))

example : IsCharRoot 3 2 2 := by norm_num [IsCharRoot]

/-- Boundary probe: `τ = 0`, `Δ = 0` (a double zero root) is neither stable nor unstable. -/
example : ¬ IsLinearlyStable 0 0 ∧ ¬ IsLinearlyUnstable 0 0 := by
  rw [isLinearlyStable_iff, isLinearlyUnstable_iff]
  norm_num

end MathlibExtTest.Biology.Dynamics.PlanarStability
