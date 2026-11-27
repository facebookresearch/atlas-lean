/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.DenseGridSquareErdosProblem658

namespace MathlibExtTest.Combinatorics.DenseGridSquareErdosProblem658

open MathlibExt.Combinatorics.DenseGridSquareErdosProblem658Wanted

-- The full grid attains the density bound at δ = 1.
example : ∀ᶠ N : ℕ in Filter.atTop,
    ∃ a b d : ℕ, 0 < d ∧ 1 ≤ a ∧ 1 ≤ b ∧ a + d ≤ N ∧ b + d ≤ N := by
  filter_upwards [denseGridContainsSquare_holds 1 zero_lt_one] with N hN
  let grid := Finset.Icc 1 N ×ˢ Finset.Icc 1 N
  have hcard : 1 * (N : ℝ) ^ 2 ≤ (grid.card : ℝ) := by
    simp [grid, pow_two]
  obtain ⟨a, b, d, hd, hab, _, _, hcorner⟩ := hN grid Finset.Subset.rfl hcard
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  obtain ⟨had, hbd⟩ := Finset.mem_product.mp hcorner
  exact ⟨a, b, d, hd, (Finset.mem_Icc.mp ha).1, (Finset.mem_Icc.mp hb).1,
    (Finset.mem_Icc.mp had).2, (Finset.mem_Icc.mp hbd).2⟩

end MathlibExtTest.Combinatorics.DenseGridSquareErdosProblem658
