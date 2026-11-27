/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HeightOneMultipleZetaSeries

open MetaMathlibExt

-- At order one the Hurwitz coefficients are all one, giving the depth-one zeta series.
example (s : ℂ) : multipleHurwitzZeta 1 s = heightOneMultipleZeta s 0 := by
  rw [multipleHurwitzZeta, heightOneMultipleZeta_zero]
  apply tsum_congr
  intro b
  simp [Nat.factorial_ne_zero]

-- The smallest shift cancels the integral weight. At depth one the series in n is conditional.
example :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Ico 2 N,
        (-1 : ℂ) ^ n / ((n : ℂ) - 1) * (∑' a : ℕ, ((a : ℂ) + 1) ^ (-(n : ℂ))))
      Filter.atTop (nhds (∫ r in (0 : ℝ)..1, multipleHurwitzZeta r 2)) := by
  simpa [heightOneMultipleZeta_zero, sub_eq_add_neg] using
    tendsto_alternating_heightOneMultipleZeta_integral (-1) (by decide) 0

-- At k = 1 the harmonic term and the alternating correction give the classical constants.
example :
    HasSum (fun j : ℕ => heightOneMultipleZeta 2 j - 1) 1 ∧
    HasSum (fun j : ℕ => (-1 : ℂ) ^ j * (heightOneMultipleZeta 2 j - 1)) (1 / 2) := by
  have h := hasSum_heightOneMultipleZeta_goldbach 1 (by decide)
  norm_num [Finset.Icc_self, harmonic, Finset.sum_range_one] at h ⊢
  exact h

-- At k = 2 a lower-degree Stirling coefficient survives, and the finite sum has two terms.
example :
    HasSum (fun j : ℕ => (2 : ℂ) ^ j * heightOneMultipleZeta 3 j - 1 / 4)
      (1 / 2 * (riemannZeta 2 + 3 / 2)) ∧
    HasSum (fun j : ℕ => (-1 : ℂ) ^ j * ((2 : ℂ) ^ j * heightOneMultipleZeta 3 j - 1 / 4))
      (3 / 4) := by
  have h := hasSum_heightOneMultipleZeta_goldbach 2 (by decide)
  norm_num [show Finset.Icc (1 : ℕ) 2 = {1, 2} by decide, Nat.factorial, Nat.stirlingFirst,
    harmonic, Finset.sum_range_succ, Finset.sum_insert, Nat.choose] at h ⊢
  exact h
