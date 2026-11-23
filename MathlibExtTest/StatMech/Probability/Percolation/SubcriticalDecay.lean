/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.SubcriticalDecay

/-!
# Tests for `MathlibExt.Probability.Percolation.SubcriticalDecay`

Tests the definitions `StatMech.Percolation.crossingEvent` and `crossProb` (the one-arm
probability): `0 ≤ crossProb ≤ 1`, antitonicity in `n`, and in dimension `0` (a single site, which
lies in every box) `crossingEvent 0 n = ∅` and `crossProb 0 p n = 0`. The value
`crossProb d 1 (n + 1) = 1` is tested with `SharpnessUnconditional`.
-/

@[expose] public section

open StatMech StatMech.Percolation StatMech.Lattice
open scoped NNReal

namespace MathlibExtTest.StatMech.Probability.Percolation.SubcriticalDecay

-- Range and monotonicity of the one-arm probability.
example (hp : (1 / 2 : ℝ≥0) ≤ 1) (n : ℕ) :
    0 ≤ crossProb 2 (1 / 2) hp n ∧ crossProb 2 (1 / 2) hp n ≤ 1 :=
  ⟨crossProb_nonneg _ _ _ _, crossProb_le_one _ _ _ _⟩

example (hp : (1 / 2 : ℝ≥0) ≤ 1) : crossProb 2 (1 / 2) hp 5 ≤ crossProb 2 (1 / 2) hp 3 :=
  crossProb_antitone _ _ hp (by norm_num)

-- In dimension `0` no site lies outside a box, so the crossing event is empty.
theorem crossingEvent_zero (n : ℕ) : crossingEvent 0 n = ∅ := by
  ext ω
  simp [mem_crossingEvent, mem_box]

example (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) : crossProb 0 p hp n = 0 := by
  simp [crossProb, crossingEvent_zero]

end MathlibExtTest.StatMech.Probability.Percolation.SubcriticalDecay
