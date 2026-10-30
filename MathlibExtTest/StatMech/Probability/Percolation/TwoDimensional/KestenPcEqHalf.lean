/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.TwoDimensional.KestenPcEqHalf
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.TwoDimensional.KestenPcEqHalf`

* `kesten_pc_le_half` for the step crossing function `cross p n = 0` for `p < 1/2` and `1/2`
  for `p ≥ 1/2`: `hmono` and `hdualHalf` are proved, and `hdecayToZero` reduces to the
  assumption that the one-arm probability does not decay exponentially for `p ≥ 1/2` (true by
  Kesten's theorem and RSW theory, not in the library). So `p_c ≤ 1/2` follows from that
  assumption alone, which shows how much of the content sits in `hdecayToZero`.
-/

@[expose] public section

open Filter
open scoped NNReal Topology
open StatMech StatMech.Percolation StatMech.TwoDim

namespace MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.KestenPcEqHalf

/-- The step crossing function: `0` below `1/2`, `1/2` from `1/2` on. -/
noncomputable def crossStep : ℝ≥0 → ℕ → ℝ := fun p _ => if p < 1 / 2 then 0 else 1 / 2

theorem crossStep_mono : ∀ n, ∀ p q : ℝ≥0, p ≤ q → crossStep p n ≤ crossStep q n := by
  intro n p q hpq
  unfold crossStep
  split_ifs with hp hq hq <;> norm_num
  exact absurd (lt_of_le_of_lt hpq hq) hp

theorem crossStep_half : ∀ n, crossStep (1 / 2) n = 1 / 2 := fun _ => by simp [crossStep]

/-- The hypothesis `hdecayToZero` for `crossStep`, from "no exponential decay for `p ≥ 1/2`". -/
theorem crossStep_decay
    (hno : ∀ p : ℝ≥0, 1 / 2 ≤ p → ∀ hp : p ≤ 1,
      ¬ ∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n)) :
    ∀ p : ℝ≥0, ∀ hp : p ≤ 1,
      (∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n)) →
      Tendsto (crossStep p) atTop (𝓝 0) := by
  intro p hp hdec
  by_cases h : p < 1 / 2
  · have hc : crossStep p = fun _ => 0 := funext fun _ => ite_eq_left h
    rw [hc]; exact tendsto_const_nhds
  · exact absurd hdec (hno p (not_lt.mp h) hp)

example
    (hno : ∀ p : ℝ≥0, 1 / 2 ≤ p → ∀ hp : p ≤ 1,
      ¬ ∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n)) :
    pc 2 ≤ (1 / 2 : ℝ≥0) :=
  kesten_pc_le_half crossStep crossStep_mono crossStep_half (crossStep_decay hno)

end MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.KestenPcEqHalf
