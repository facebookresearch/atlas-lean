/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.TwoDimensional.Kesten
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.TwoDimensional.Kesten`

* For any crossing function with `hdualHalf` (`cross (1/2) n = 1/2`), the hypothesis
  `hpercToOne` holds if and only if `θ(1/2) = 0`: one direction is `theta_half_eq_zero`, the
  other is immediate. This records that the hypotheses of `theta_half_eq_zero`,
  `half_mem_subcriticalSet` and `half_le_pc` are equivalent to Harris's theorem, which the
  library does not prove; so they are instantiated here only under the assumption `θ(1/2) = 0`.
* `pc_le_half` and `pc_eq_half` are not instantiated (their `hdecayToZero` is equivalent to
  non-exponential decay above `1/2`, see `MathlibExt.Probability.Percolation.TwoDimensional.KestenPcEqHalf`).
-/

@[expose] public section

open Filter
open scoped NNReal Topology
open StatMech StatMech.Percolation StatMech.TwoDim

namespace MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.Kesten

/-- The constant crossing function `1/2`. -/
noncomputable def crossHalf : ℝ≥0 → ℕ → ℝ := fun _ _ => 1 / 2

example (h12 : (1 / 2 : ℝ≥0) ≤ 1) :
    (0 < theta 2 (1 / 2) h12 → Tendsto (crossHalf (1 / 2)) atTop (𝓝 1)) ↔
      theta 2 (1 / 2) h12 = 0 :=
  ⟨fun h => theta_half_eq_zero h12 crossHalf (fun _ => rfl) h,
    fun h hpos => absurd h hpos.ne'⟩

example (h12 : (1 / 2 : ℝ≥0) ≤ 1) (hθ : theta 2 (1 / 2) h12 = 0) : (1 / 2 : ℝ≥0) ≤ pc 2 :=
  half_le_pc h12 crossHalf (fun _ => rfl) (fun hpos => absurd hθ hpos.ne')

example (h12 : (1 / 2 : ℝ≥0) ≤ 1) (hθ : theta 2 (1 / 2) h12 = 0) :
    (1 / 2 : ℝ≥0) ∈ subcriticalSet 2 :=
  half_mem_subcriticalSet h12 crossHalf (fun _ => rfl) (fun hpos => absurd hθ hpos.ne')

end MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.Kesten
