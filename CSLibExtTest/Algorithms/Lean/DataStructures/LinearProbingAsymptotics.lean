/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.LinearProbingAsymptotics

/-!
# Tests for the limits of Knuth's sums

A non-degenerate instance of `tendsto_knuthE`: a half-full table, `n N = ⌊N / 2⌋` and
`α = 1 / 2`, for which `E_1(N, ⌊N / 2⌋ + 1) → 4` and so Knuth's `M → (1 + 4) / 2 = 5 / 2`, the
value `2.500` of his table at load factor `0.5`.
-/

open Filter Topology

namespace Cslib.Algorithms.Lean.LinearProbing.Test

open Cslib.Algorithms.Lean.LinearProbing

/-- `⌊N / 2⌋ / N → 1 / 2`. -/
theorem tendsto_half_div :
    Tendsto (fun N : ℕ => ((N / 2 : ℕ) : ℝ) / N) atTop (𝓝 (1 / 2)) := by
  have hlow : Tendsto (fun N : ℕ => (1 : ℝ) / 2 - (1 / 2) * (1 / (N : ℝ))) atTop
      (𝓝 (1 / 2)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ) / 2)).sub
      ((tendsto_one_div_atTop_nhds_zero_nat).const_mul (1 / 2 : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [le_div_iff₀ hN']
    have h2 : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by
      have : N ≤ 2 * (N / 2) + 1 := by omega
      exact_mod_cast this
    field_simp
    linarith
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_iff₀ hN']
    have h2 : 2 * ((N / 2 : ℕ) : ℝ) ≤ N := by
      have : 2 * (N / 2) ≤ N := Nat.mul_div_le N 2
      exact_mod_cast this
    linarith

/-- In a half-full table `E_1(N, ⌊N / 2⌋ + 1) → 1 / (1 - 1 / 2) ^ 2 = 4`. -/
example : Tendsto (fun N : ℕ => (knuthE 1 N (N / 2 + 1) : ℝ)) atTop
    (𝓝 (1 / (1 - 1 / 2) ^ (1 + 1))) :=
  tendsto_knuthE 1 (by norm_num) (by norm_num) (fun N => N / 2) tendsto_half_div

/-- The degenerate instance `α = 0`, `n N = 0`: `E_0(N, 1) = 1`. -/
example : Tendsto (fun N : ℕ => (knuthE 0 N (0 + 1) : ℝ)) atTop (𝓝 (1 / (1 - 0) ^ (0 + 1))) :=
  tendsto_knuthE 0 le_rfl (by norm_num) (fun _ => 0) (by simp)

end Cslib.Algorithms.Lean.LinearProbing.Test
