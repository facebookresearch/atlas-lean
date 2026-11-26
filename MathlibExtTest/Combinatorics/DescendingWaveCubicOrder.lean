/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.DescendingWaveCubicOrder
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MathlibExt.Combinatorics.DescendingWaveColoringErdosProblem781Wanted

-- The proved statement is the cubic-order statement itself.
example : waveNumberCubicOrder := waveNumberCubicOrder_holds

-- For all large `k` some number forces a `k`-term wave, so the wave number is finite.
example : ∀ᶠ k : ℕ in Filter.atTop, ∃ n, ForcesMonochromaticWave k n := by
  obtain ⟨c, C, -, h⟩ := waveNumberCubicOrder_holds
  filter_upwards [h] with k hk
  exact ⟨_, hk.2⟩

-- The cubic lower bound eventually rules out the quadratic value `k ^ 2 - k + 1`, which
-- Brown, Erdős and Freedman asked about, so the lower bound is not vacuous.
example : ∀ᶠ k : ℕ in Filter.atTop, ¬ ForcesMonochromaticWave k (k ^ 2 - k + 1) := by
  obtain ⟨c, C, hc, h⟩ := waveNumberCubicOrder_holds
  filter_upwards [h, Filter.eventually_ge_atTop (⌈1 / c⌉₊ + 1)] with k hk hkc hforce
  have hk1 : 1 ≤ k := le_trans (Nat.le_add_left 1 _) hkc
  have hsq : k ^ 2 - k + 1 ≤ k ^ 2 := by
    have : k ≤ k ^ 2 := by nlinarith
    omega
  have hlow : c * (k : ℝ) ^ 3 ≤ (k : ℝ) ^ 2 :=
    (hk.1 _ hforce).trans (by exact_mod_cast hsq)
  have hck : 1 < c * (k : ℝ) := by
    have h1 : 1 / c < (k : ℝ) := by
      have h2 : (⌈1 / c⌉₊ : ℝ) + 1 ≤ k := by exact_mod_cast hkc
      linarith [Nat.le_ceil (1 / c)]
    rwa [div_lt_iff₀ hc, mul_comm] at h1
  have hk0 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  nlinarith
