/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.SpectralLinearStatistics

@[expose] public section

open scoped NNReal

namespace MathlibExtTest.Analysis.InnerProductSpace.SpectralLinearStatistics

/-- With `f = id` (`1`-Lipschitz), the sums of the eigenvalues differ by at most
`√n ‖A - B‖_F`. -/
example {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    |∑ i, hA.eigenvalues i - ∑ i, hB.eigenvalues i| ≤
      Real.sqrt n * Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j - B i j)) := by
  simpa using hA.abs_sum_sub_sum_le_of_lipschitzWith hB (f := id) LipschitzWith.id

/-- Normalised form for the empirical spectral distributions: a `1`-Lipschitz statistic such as
`|x|` moves by at most `‖A - B‖_F / √n`. -/
example {n : ℕ} (hn : 0 < n) {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    abs ((n : ℝ)⁻¹ * ∑ i, |hA.eigenvalues i| - (n : ℝ)⁻¹ * ∑ i, |hB.eigenvalues i|) ≤
      Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j - B i j)) / Real.sqrt n := by
  have h := hA.abs_sum_sub_sum_le_of_lipschitzWith hB (f := fun x => |x|) (L := 1)
    (LipschitzWith.of_dist_le_mul fun x y => by
      simpa [Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn'.le
  rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hn'), le_div_iff₀ (Real.sqrt_pos.mpr hn')]
  calc (n : ℝ)⁻¹ * abs (∑ i, |hA.eigenvalues i| - ∑ i, |hB.eigenvalues i|) * Real.sqrt n
      ≤ (n : ℝ)⁻¹ * (Real.sqrt n * Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j - B i j))) *
          Real.sqrt n := by
        gcongr; simpa using h
    _ = Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j - B i j)) := by
        rw [mul_comm (Real.sqrt n) _, mul_assoc, mul_assoc, hs]; field_simp

end MathlibExtTest.Analysis.InnerProductSpace.SpectralLinearStatistics
