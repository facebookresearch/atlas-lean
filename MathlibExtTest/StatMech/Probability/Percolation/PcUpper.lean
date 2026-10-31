/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.PcUpper
public import MathlibExt.Probability.Percolation.SharpnessTheorem

/-!
# Tests for `MathlibExt.Probability.Percolation.PcUpper`

Tests the Peierls-series definitions `StatMech.Percolation.pcUpperBound` and `pcRatio`
(`pcUpperBound 1 = 0`, `pcRatio 1 = 0`, `pcRatio (7/8) = 1/2`), the unconditional
`exists_p_lt_one_pcUpperBound_lt_one`, and the named hypothesis `PcContourBound`, proved at `p = 1`
(from `θ_2(1) = 1`); `theta_pos_of_contourBound` is then applied at `p = 1`. The headline
`pc_lt_one` needs `PcContourBound` for every `p` above some `p₀ < 1`, which the library does not
prove; it is restated with that hypothesis.
-/

@[expose] public section

open StatMech StatMech.Percolation StatMech.Lattice
open scoped NNReal

namespace MathlibExtTest.StatMech.Probability.Percolation.PcUpper

-- `pcUpperBound 1 = 0`: every summand `ℓ 4^ℓ 0^ℓ` vanishes.
theorem pcUpperBound_one : pcUpperBound 1 = 0 := by
  have h : (fun ℓ : ℕ => (ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - 1) ^ ℓ) = fun _ => 0 := by
    funext ℓ
    cases ℓ <;> simp
  simp only [pcUpperBound, h, tsum_zero]

example : pcRatio 1 = 0 := by simp [pcRatio]

example : pcRatio (7 / 8) = 1 / 2 := by norm_num [pcRatio]

-- The Peierls series drops below `1` near `p = 1`.
example : ∃ p₀ : ℝ, p₀ < 1 ∧ ∀ p : ℝ, p₀ < p → p ≤ 1 → pcUpperBound p < 1 := by
  obtain ⟨p₀, h₀, h⟩ := exists_p_lt_one_pcUpperBound_lt_one
  exact ⟨p₀, h₀, fun p hp hp1 => h p hp hp1⟩

-- `PcContourBound` holds at `p = 1`.
theorem pcContourBound_one (h1 : (1 : ℝ≥0) ≤ 1) : PcContourBound 1 h1 := by
  rw [PcContourBound, theta_one_eq_one two_pos h1, NNReal.coe_one, pcUpperBound_one]
  norm_num

-- `theta_pos_of_contourBound` with both hypotheses discharged at `p = 1`.
example (h1 : (1 : ℝ≥0) ≤ 1) : 0 < theta 2 1 h1 :=
  theta_pos_of_contourBound h1 (pcContourBound_one h1)
    (by rw [NNReal.coe_one, pcUpperBound_one]; norm_num)

-- The headline, with its (unproved) geometric hypothesis inlined.
example (hGeom : ∃ p₀ : ℝ, p₀ < 1 ∧
      ∀ (p : ℝ≥0) (hp : p ≤ 1), (p₀ : ℝ) < (p : ℝ) → PcContourBound p hp) :
    0 < pc 2 ∧ pc 2 < 1 :=
  pc_pos_and_lt_one hGeom

end MathlibExtTest.StatMech.Probability.Percolation.PcUpper
