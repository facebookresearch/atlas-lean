/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.SharpnessTheorem
public import MathlibExt.Probability.Percolation.PcUpperEnclosure

/-!
# Tests for `MathlibExt.Probability.Percolation.SharpnessUnconditional`

Tests the headline `StatMech.Percolation.sharp_phase_transition` at `d = 1` and `d = 2`:

* item 1 gives `p̃_c = p_c` for `d = 1, 2`, and with `tildePc_pos` the consequence `0 < p_c(2)`;
* item 2 is applied to the explicit density `p = 1/9 ∈ tildePcSet 2` (witness `S = {0}`,
  `φ_{1/9}({0}) ≤ 4/9 < 1`), giving exponential decay of the one-arm probability and `θ_2(1/9) = 0`;
* item 3 needs some `q` with `p̃_c < q < 1`; `p̃_c(2) < 1` is not proved unconditionally in the
  library, so item 3 is instantiated under `PcAnchoredEnclosure` (via `pc_lt_one_of_enclosure`),
  giving `θ_2(q) > 0` for an explicit `q`.

Also checks the computed values `crossProb d 1 (n + 1) = 1`, `θ_d(1) = 1`, and `p̃_c(d) ≤ 1`.
-/

@[expose] public section

open StatMech StatMech.Percolation StatMech.Lattice
open scoped NNReal

namespace MathlibExtTest.StatMech.Probability.Percolation.SharpnessUnconditional

-- Item 1 at `d = 1` and `d = 2`: `p̃_c = p_c`.
example : tildePc 1 = pc 1 := (sharp_phase_transition (d := 1) one_pos).1

example : tildePc 2 = pc 2 := (sharp_phase_transition (d := 2) two_pos).1

-- Consequence: `0 < p_c(2)` from `p̃_c(2) > 0` and item 1.
example : (0 : ℝ) < pc 2 := by
  rw [← (sharp_phase_transition (d := 2) two_pos).1]
  exact tildePc_pos two_pos

-- `p̃_c(d) ≤ 1`: every element of `tildePcSet d` is at most `1`.
example (d : ℕ) : tildePc d ≤ 1 := by
  unfold tildePc
  rcases (tildePcSet d).eq_empty_or_nonempty with h | h
  · rw [h, csSup_empty]; exact bot_le
  · exact csSup_le h fun q hq => (mem_tildePcSet.mp hq).1

-- The density `1/9` lies in `tildePcSet 2`, with witness `S = {0}`: `φ ≤ (1/9) · 4 < 1`.
theorem nineth_mem_tildePcSet : (1 / 9 : ℝ≥0) ∈ tildePcSet 2 := by
  have hp : (1 / 9 : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by norm_num)]; norm_num
  refine ⟨hp, {origin 2}, Finset.mem_singleton_self _, ?_⟩
  have hcard : ((boundaryEdges 2 {origin 2}).card : ℝ) ≤ 4 := by
    have := card_boundaryEdges_le (d := 2) {origin 2}
    rw [Finset.card_singleton] at this
    exact_mod_cast this
  calc phi 2 (1 / 9) hp {origin 2}
      ≤ ((1 / 9 : ℝ≥0) : ℝ) * (boundaryEdges 2 {origin 2}).card := phi_le_mul_card _ hp _
    _ ≤ ((1 / 9 : ℝ≥0) : ℝ) * 4 := mul_le_mul_of_nonneg_left hcard (by positivity)
    _ < 1 := by push_cast; norm_num

-- Item 2 at `p = 1/9`, `d = 2`: the one-arm probability decays exponentially.
example (hp : (1 / 9 : ℝ≥0) ≤ 1) :
    ∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 (1 / 9) hp n ≤ C * Real.exp (-c * n) :=
  (sharp_phase_transition (d := 2) two_pos).2.1 _ nineth_mem_tildePcSet hp

-- Concrete consequence of item 2: `θ_2(1/9) = 0`.
example (hp : (1 / 9 : ℝ≥0) ≤ 1) : theta 2 (1 / 9) hp = 0 :=
  theta_eq_zero_of_crossProb_decay _ hp
    ((sharp_phase_transition (d := 2) two_pos).2.1 _ nineth_mem_tildePcSet hp)

-- Computed values at `p = 1`: `crossProb d 1 (n + 1) = 1` and `θ_d(1) = 1`.
example (h1 : (1 : ℝ≥0) ≤ 1) (n : ℕ) : crossProb 2 1 h1 (n + 1) = 1 := crossProb_one two_pos h1 n

example (h1 : (1 : ℝ≥0) ≤ 1) : theta 1 1 h1 = 1 := theta_one_eq_one one_pos h1

-- Item 3 at `d = 2`, under `PcAnchoredEnclosure` (which yields `p̃_c(2) < 1`): for
-- `q = (p̃_c + 1)/2`, the mean-field bound holds and gives `θ_2(q) > 0`.
example (henc : PcAnchoredEnclosure) :
    ∃ q : ℝ≥0, ∃ hq : q ≤ 1, tildePc 2 < q ∧ 0 < theta 2 q hq := by
  obtain ⟨h1, -, h3⟩ := sharp_phase_transition (d := 2) two_pos
  have hlt : tildePc 2 < 1 := h1 ▸ pc_lt_one_of_enclosure henc
  have hltR : (tildePc 2 : ℝ) < 1 := by exact_mod_cast hlt
  have hpos : (0 : ℝ) < tildePc 2 := tildePc_pos two_pos
  set q : ℝ≥0 := (tildePc 2 + 1) / 2 with hq_def
  have hqR : (q : ℝ) = ((tildePc 2 : ℝ) + 1) / 2 := by rw [hq_def]; push_cast; ring
  have hq1 : q ≤ 1 := by
    have : (q : ℝ) ≤ 1 := by rw [hqR]; linarith
    exact_mod_cast this
  have hgt : tildePc 2 < q := by
    have : (tildePc 2 : ℝ) < q := by rw [hqR]; linarith
    exact_mod_cast this
  have hqlt : (q : ℝ) < 1 := by rw [hqR]; linarith
  refine ⟨q, hq1, hgt, lt_of_lt_of_le ?_ (h3 q hq1 hgt hqlt)⟩
  have hgtR : (tildePc 2 : ℝ) < q := by exact_mod_cast hgt
  apply div_pos (by linarith)
  exact mul_pos (by linarith) (by linarith)

end MathlibExtTest.StatMech.Probability.Percolation.SharpnessUnconditional
