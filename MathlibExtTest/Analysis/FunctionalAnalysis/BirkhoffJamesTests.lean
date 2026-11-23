/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.BirkhoffJames

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.NormNum

/-!
# Tests for Birkhoff–James orthogonality and the duality mapping

On `EuclideanSpace ℝ (Fin 2)` and `EuclideanSpace ℂ (Fin 2)` we check the
inner-product characterization (the standard basis vectors are
Birkhoff–James orthogonal, a vector is not Birkhoff–James orthogonal to a
vector with a nonzero first coordinate), the norming-functional and
duality-mapping characterizations, homogeneity, and the self-orthogonality
criterion.
-/

namespace MathlibExtTest.Analysis.FunctionalAnalysis.BirkhoffJamesTests

open MathlibExt.Analysis.FunctionalAnalysis.BirkhoffJames

/-- The first standard basis vector of `ℝ²` has norm `1`. -/
theorem norm_e1 : ‖(!₂[1, 0] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
  simp [PiLp.norm_eq_of_L2, Fin.sum_univ_two]

/-- The first standard basis vector of `ℝ²` is nonzero. -/
theorem e1_ne_zero : (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [norm_e1]; norm_num)

/-- In `ℝ²`, `e₁` is Birkhoff–James orthogonal to `e₂`. -/
theorem real_e1_birkhoffJames_e2 :
    BirkhoffJamesOrthogonal ℝ (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) !₂[0, 1] := by
  rw [birkhoffJamesOrthogonal_iff_inner_eq_zero]
  simp [PiLp.inner_apply, Fin.sum_univ_two]

/-- In `ℝ²`, `e₁` is not Birkhoff–James orthogonal to `(1, 1)`. -/
theorem real_e1_not_birkhoffJames_diag :
    ¬ BirkhoffJamesOrthogonal ℝ (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
      !₂[1, 1] := by
  rw [birkhoffJamesOrthogonal_iff_inner_eq_zero]
  simp [PiLp.inner_apply, Fin.sum_univ_two]

/-- In `ℝ²`, `e₁` is not Birkhoff–James orthogonal to itself. -/
theorem real_e1_not_birkhoffJames_self :
    ¬ BirkhoffJamesOrthogonal ℝ (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
      !₂[1, 0] := by
  rw [birkhoffJamesOrthogonal_self_iff]
  exact e1_ne_zero

/-- In `ℂ²`, `e₁` is Birkhoff–James orthogonal to `e₂`. -/
theorem complex_e1_birkhoffJames_e2 :
    BirkhoffJamesOrthogonal ℂ (!₂[1, 0] : EuclideanSpace ℂ (Fin 2)) !₂[0, 1] := by
  rw [birkhoffJamesOrthogonal_iff_inner_eq_zero]
  simp [PiLp.inner_apply, Fin.sum_univ_two]

/-- In `ℂ²`, `e₁` is not Birkhoff–James orthogonal to `(i, 0)`. -/
theorem complex_e1_not_birkhoffJames_ie1 :
    ¬ BirkhoffJamesOrthogonal ℂ (!₂[1, 0] : EuclideanSpace ℂ (Fin 2))
      !₂[Complex.I, 0] := by
  rw [birkhoffJamesOrthogonal_iff_inner_eq_zero]
  simp [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]

/-- The norming-functional characterization on the `ℝ²` example. -/
theorem real_e1_exists_norming :
    ∃ f : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ, ‖f‖ = 1 ∧
      f !₂[1, 0] = ‖(!₂[1, 0] : EuclideanSpace ℝ (Fin 2))‖ ∧ f !₂[0, 1] = 0 :=
  (birkhoffJamesOrthogonal_iff_exists_norming e1_ne_zero).mp real_e1_birkhoffJames_e2

/-- The duality-mapping characterization on the `ℝ²` example. -/
theorem real_e1_duality_vanishes :
    ∃ f ∈ dualityMapping ℝ (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)), f !₂[0, 1] = 0 :=
  birkhoffJamesOrthogonal_iff_exists_dualityMapping.mp real_e1_birkhoffJames_e2

/-- Homogeneity on the `ℝ²` example: `(2 • e₁)` is Birkhoff–James orthogonal
to `(3 • e₂)`. -/
theorem real_smul_birkhoffJames :
    BirkhoffJamesOrthogonal ℝ ((2 : ℝ) • !₂[1, 0] : EuclideanSpace ℝ (Fin 2))
      ((3 : ℝ) • !₂[0, 1]) :=
  birkhoffJamesOrthogonal_smul_left_right real_e1_birkhoffJames_e2

/-- The duality mapping at `e₁` in `ℝ²` is nonempty. -/
theorem real_e1_duality_nonempty :
    (dualityMapping ℝ (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))).Nonempty :=
  dualityMapping_nonempty _

end MathlibExtTest.Analysis.FunctionalAnalysis.BirkhoffJamesTests
