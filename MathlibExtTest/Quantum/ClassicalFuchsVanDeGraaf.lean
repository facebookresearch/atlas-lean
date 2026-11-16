/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.ClassicalFuchsVanDeGraaf
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Quantum.ClassicalFuchsVanDeGraaf

open MathlibExt.Probability.MarkovMixing MathlibExt.Quantum.ClassicalFuchsVanDeGraaf

/-! ### Distinct point masses on `Fin 2` -/

/-- Distinct point masses are at total variation distance `1`, which pins the `1/2`
normalization. -/
theorem tvDist_pointMasses : tvDist ![(1 : ℝ), 0] ![0, 1] = 1 := by
  norm_num [tvDist, Fin.sum_univ_two]

/-- Distinct point masses have Bhattacharyya coefficient `0`. -/
theorem bhattacharyyaCoeff_pointMasses : bhattacharyyaCoeff ![(1 : ℝ), 0] ![0, 1] = 0 := by
  simp [bhattacharyyaCoeff, Fin.sum_univ_two]

/-- The lower bound applies to distinct point masses (with equality `1 - 0 = 1`). -/
example : 1 - bhattacharyyaCoeff ![(1 : ℝ), 0] ![0, 1] ≤ tvDist ![(1 : ℝ), 0] ![0, 1] :=
  one_sub_bhattacharyyaCoeff_le_tvDist _ _ (by simp [Fin.forall_fin_two])
    (by simp [Fin.forall_fin_two]) (by simp [Fin.sum_univ_two]) (by simp [Fin.sum_univ_two])

/-- The upper bound applies to distinct point masses (with equality `1 = √(1 - 0 ^ 2)`). -/
example : tvDist ![(1 : ℝ), 0] ![0, 1]
    ≤ Real.sqrt (1 - bhattacharyyaCoeff ![(1 : ℝ), 0] ![0, 1] ^ 2) :=
  tvDist_le_sqrt_one_sub_bhattacharyyaCoeff_sq _ _ (by simp [Fin.forall_fin_two])
    (by simp [Fin.forall_fin_two]) (by simp [Fin.sum_univ_two]) (by simp [Fin.sum_univ_two])

/-- Both bounds are attained by distinct point masses. -/
example : tvDist ![(1 : ℝ), 0] ![0, 1]
      = Real.sqrt (1 - bhattacharyyaCoeff ![(1 : ℝ), 0] ![0, 1] ^ 2) ∧
    1 - bhattacharyyaCoeff ![(1 : ℝ), 0] ![0, 1] = tvDist ![(1 : ℝ), 0] ![0, 1] := by
  rw [tvDist_pointMasses, bhattacharyyaCoeff_pointMasses]
  norm_num

/-! ### An overlapping pair: `p = (1/4, 3/4)` and `q = (1, 0)` -/

/-- The Bhattacharyya coefficient of the overlapping pair is `√(1/4) = 1/2`. -/
theorem bhattacharyyaCoeff_overlap : bhattacharyyaCoeff ![(1 / 4 : ℝ), 3 / 4] ![1, 0] = 1 / 2 := by
  rw [bhattacharyyaCoeff, Fin.sum_univ_two]
  have h0 : Real.sqrt (![(1 / 4 : ℝ), 3 / 4] 0 * ![(1 : ℝ), 0] 0) = 1 / 2 := by
    rw [show ![(1 / 4 : ℝ), 3 / 4] 0 * ![(1 : ℝ), 0] 0 = (1 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h1 : Real.sqrt (![(1 / 4 : ℝ), 3 / 4] 1 * ![(1 : ℝ), 0] 1) = 0 := by simp
  rw [h0, h1, add_zero]

/-- The total variation distance of the overlapping pair is `3/4`. -/
theorem tvDist_overlap : tvDist ![(1 / 4 : ℝ), 3 / 4] ![1, 0] = 3 / 4 := by
  rw [tvDist, Fin.sum_univ_two]
  norm_num [abs_of_neg, abs_of_pos]

/-- On the overlapping pair the lower bound is strict: `1 - 1/2 < 3/4`. -/
example : 1 - bhattacharyyaCoeff ![(1 / 4 : ℝ), 3 / 4] ![1, 0]
    < tvDist ![(1 / 4 : ℝ), 3 / 4] ![1, 0] := by
  rw [bhattacharyyaCoeff_overlap, tvDist_overlap]
  norm_num

/-- The upper bound, applied to the overlapping pair, gives `3/4 ≤ √(1 - (1/2) ^ 2)`. -/
example : (3 / 4 : ℝ) ≤ Real.sqrt (1 - (1 / 2) ^ 2) := by
  have h := tvDist_le_sqrt_one_sub_bhattacharyyaCoeff_sq ![(1 / 4 : ℝ), 3 / 4] ![1, 0]
    (by norm_num [Fin.forall_fin_two]) (by norm_num [Fin.forall_fin_two])
    (by norm_num [Fin.sum_univ_two]) (by norm_num [Fin.sum_univ_two])
  rwa [tvDist_overlap, bhattacharyyaCoeff_overlap] at h

end MathlibExtTest.Quantum.ClassicalFuchsVanDeGraaf

end
