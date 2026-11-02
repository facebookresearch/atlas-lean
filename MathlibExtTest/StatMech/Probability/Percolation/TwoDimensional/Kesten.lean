/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.TwoDimensional.Kesten
public import Mathlib.Tactic

/-!
# Tests for `MathlibExt.Probability.Percolation.TwoDimensional.Kesten`

* `pc_le_half` applied under its stated sharpness hypotheses. This is a signature smoke test
  only: the hypotheses are not discharged here.

The former `theta_half_eq_zero`, `half_mem_subcriticalSet`, `half_le_pc`, and `pc_eq_half`
capstones were removed: their hypotheses were together equivalent to Harris's theorem
`θ(1/2) = 0`, which the library does not prove, so they assumed the substantive content
under another name. Their tests were removed with them.
-/

@[expose] public section

open Filter
open scoped NNReal Topology
open StatMech StatMech.Percolation StatMech.TwoDim

namespace MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.Kesten

example
    (hsharp : tildePc 2 = pc 2)
    (cross : ℝ≥0 → ℕ → ℝ)
    (hsub : ∀ p ∈ tildePcSet 2, ∀ hp : p ≤ 1,
        ∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n))
    (hmono : ∀ n, ∀ p q : ℝ≥0, p ≤ q → cross p n ≤ cross q n)
    (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
    (hdecayToZero : ∀ p : ℝ≥0, ∀ hp : p ≤ 1,
        (∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n)) →
        Tendsto (cross p) atTop (𝓝 0)) :
    pc 2 ≤ (1 / 2 : ℝ≥0) :=
  pc_le_half hsharp cross hsub hmono hdualHalf hdecayToZero

end MathlibExtTest.StatMech.Probability.Percolation.TwoDimensional.Kesten
