/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Susceptibility

@[expose] public section

open MeasureTheory StatMech StatMech.Percolation StatMech.Lattice
open scoped NNReal

namespace MathlibExtTest.Probability.Percolation.Susceptibility

/-- The square `Λ_1 ⊆ ℤ²` has `9` sites. -/
example : (boxFinset 2 1).card = 9 := by
  rw [card_boxFinset]; norm_num

/-- Non-vacuity on `ℤ²`: at the density `p_c(2)/2 ∈ (0, p_c(2))` the susceptibility is finite. -/
example : ∃ p : ℝ≥0, 0 < p ∧ ∃ hp : p ≤ 1,
    Summable fun x : Site 2 =>
      (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
        {ω | Connected 2 ω (origin 2) x} := by
  have hpc : 0 < pc 2 := pc_pos (by norm_num)
  have hlt : pc 2 / 2 < pc 2 := NNReal.half_lt_self hpc.ne'
  have hp : pc 2 / 2 ≤ 1 := hlt.le.trans pc_le_one
  exact ⟨pc 2 / 2, by positivity, hp, summable_connProb_of_lt_pc (by norm_num) hp hlt⟩

/-- The one-arm comparison at a site of sup-norm `1`. -/
example (p : ℝ≥0) (hp : p ≤ 1) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp).real
        {ω | Connected 2 ω (origin 2) ![1, 0]} ≤ crossProb 2 p hp 1 := by
  have h : supNorm (![1, 0] : Site 2) = 1 := by decide
  simpa [h] using connProb_le_crossProb (d := 2) (by norm_num) p hp (x := ![1, 0]) (by rw [h])

end MathlibExtTest.Probability.Percolation.Susceptibility
