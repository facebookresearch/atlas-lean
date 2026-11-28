/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CentralBinomialProductAsymptotics

open Filter Topology MetaMathlibExt

-- The Glaisher–Kinkelin factor cancels between the two normalized products.
example : Tendsto (fun m : ℕ =>
    ((∏ n ∈ Finset.Icc 1 m, (catalan n : ℝ)) /
      (2 ^ ((m : ℝ) ^ 2) * (4 * Real.exp 3 / Real.pi) ^ ((m : ℝ) / 2) /
        (m : ℝ) ^ (3 * (m : ℝ) / 2 + 15 / 8))) /
    ((∏ n ∈ Finset.Icc 1 m, (n.centralBinom : ℝ)) /
      (2 ^ ((m : ℝ) ^ 2) * (4 * Real.exp 1 / Real.pi) ^ ((m : ℝ) / 2) /
        (m : ℝ) ^ ((m : ℝ) / 2 + 3 / 8))))
    atTop (𝓝 ((2 * Real.pi) ^ (-(1 : ℝ) / 2))) := by
  obtain ⟨hb, hc⟩ := tendsto_prod_centralBinom_catalan_div
  have hA : 0 < glaisherKinkelinConstant := Real.exp_pos _
  have h := hc.div hb (by positivity)
  rwa [mul_div_cancel_left₀ _ (by positivity)] at h

-- For the first two factors the products differ by the expected factor of 3!.
example : (∏ n ∈ Finset.Icc 1 2, n.centralBinom) = 12 ∧
    (∏ n ∈ Finset.Icc 1 2, catalan n) = 2 := by
  simp_rw [catalan_eq_centralBinom_div]
  decide

-- The Pascal-row limit can also be used directly in terms of the Glaisher–Kinkelin constant.
example : Tendsto (fun n : ℕ => (∏ k ∈ Finset.range (n + 1), (n.choose k : ℝ)) /
    (Real.exp ((n : ℝ) ^ 2 / 2 + n) /
      ((2 * Real.pi) ^ ((n : ℝ) / 2) * (n : ℝ) ^ ((n : ℝ) / 2 + 1 / 3))))
    atTop (𝓝 (glaisherKinkelinConstant ^ 2 / ((2 * Real.pi) ^ ((1 : ℝ) / 2) *
      Real.exp (1 / 12)))) := by
  obtain ⟨h, hc⟩ := tendsto_prod_choose_row_div
  rwa [hc] at h

-- A singleton row and a row with nontrivial interior entries.
example : (∏ k ∈ Finset.range (0 + 1), (0 : ℕ).choose k) = 1 ∧
    (∏ k ∈ Finset.range (4 + 1), (4 : ℕ).choose k) = 96 := by
  decide
