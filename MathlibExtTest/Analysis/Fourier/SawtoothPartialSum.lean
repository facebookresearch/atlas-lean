/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.SawtoothPartialSum

/-!
# Tests for the Fourier partial sums of the sawtooth
-/

@[expose] public section

open Finset Real

/-- At `x = 1/2`, `M = 1`: `|0 + sin π / π| ≤ 1 / (2π ‖1/2‖)`. -/
example : |Int.fract (1 / 2 : ℝ) - 1 / 2 + ∑ k ∈ range 1,
    Real.sin (2 * π * ((k : ℝ) + 1) * (1 / 2)) / (π * ((k : ℝ) + 1))| ≤
      1 / (2 * π * (1 : ℕ) * ‖((1 / 2 : ℝ) : AddCircle (1 : ℝ))‖) :=
  abs_fract_sub_half_add_sum_sin_le one_pos (by norm_num [Int.fract_eq_self])

/-- Negative arguments are allowed. -/
example : |Int.fract (-1 / 3 : ℝ) - 1 / 2 + ∑ k ∈ range 5,
    Real.sin (2 * π * ((k : ℝ) + 1) * (-1 / 3)) / (π * ((k : ℝ) + 1))| ≤
      1 / (2 * π * (5 : ℕ) * ‖((-1 / 3 : ℝ) : AddCircle (1 : ℝ))‖) := by
  refine abs_fract_sub_half_add_sum_sin_le (by norm_num) ?_
  rw [Int.fract, show ⌊(-1 / 3 : ℝ)⌋ = -1 by norm_num [Int.floor_eq_iff]]
  norm_num

/-- **Constant functions.** With `K = 0` the bound forces the symmetric partial sums of the
Fourier coefficients of a constant `c` to equal `c`. -/
example (c : ℂ) :
    ‖∑ m ∈ Icc (-(2 : ℕ) : ℤ) ((2 : ℕ) : ℤ), fourierCoeffOn zero_lt_one (fun _ => c) m -
      (c + c) / 2‖ ≤ 20 * 0 * Real.log (2 : ℕ) / (2 : ℕ) :=
  norm_sum_fourierCoeffOn_sub_average_le (f' := fun _ => 0) continuousOn_const
    (fun _ _ => hasDerivAt_const _ _) (fun _ _ => by simp) le_rfl

/-- **The identity on `[0, 1]`**, whose periodic extension jumps from `1` to `0`: the symmetric
partial sums at `0` approach `1 / 2`. -/
example (M : ℕ) (hM : 2 ≤ M) :
    ‖∑ m ∈ Icc (-(M : ℤ)) (M : ℤ), fourierCoeffOn zero_lt_one (fun x : ℝ => (x : ℂ)) m -
      (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ)) / 2‖ ≤ 20 * 1 * Real.log M / M :=
  norm_sum_fourierCoeffOn_sub_average_le (f' := fun _ => 1) (by fun_prop)
    (fun x _ => (hasDerivAt_id x).ofReal_comp) (fun _ _ => by simp) hM
