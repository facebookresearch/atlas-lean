/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.FisherKPP

@[expose] public section

open Real Filter Topology
open MathlibExt.Biology.Dynamics.FisherKPP

namespace MathlibExtTest.Biology.Dynamics.FisherKPP

/-- Non-vacuity witness: the Ablowitz–Zeppetella front `(1 + e^{z/√6})⁻²` for `D = r = C = 1`. -/
example : IsFront 1 1 (azSpeed 1 1) (azWave 1 1 1) (azWaveDeriv 1 1 1) :=
  isFront_azWave one_pos one_pos one_pos

/-- With `D = r = 1` the Ablowitz–Zeppetella speed is `5/√6`. -/
example : azSpeed 1 1 = 5 / √6 := by
  rw [azSpeed, one_mul, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 6), Real.sqrt_one]
  ring

/-- It exceeds the minimal speed `2`. -/
example : 2 * √(1 * 1) < azSpeed 1 1 := two_mul_sqrt_lt_azSpeed one_pos one_pos

/-- At the midpoint `z = 0` the front with `C = 1` takes the value `1/4`. -/
example : azWave 1 1 1 0 = 1 / 4 := by
  norm_num [azWave]

/-- No front of speed `1` when `D = r = 1` (`1 < 4 = 4 r D`). -/
example (U U' : ℝ → ℝ) : ¬ IsFront 1 1 1 U U' :=
  not_isFront_of_sq_lt one_pos one_pos (by norm_num)

/-- No front of speed `0` (a standing wave), and none of negative speed below the threshold. -/
example (U U' : ℝ → ℝ) : ¬ IsFront 2 3 (-4) U U' :=
  not_isFront_of_sq_lt (by norm_num) (by norm_num) (by norm_num)

/-- The constant `0` is a wave profile of every speed (it is not a front). -/
example (D r c : ℝ) : IsWaveProfile D r c (fun _ => 0) (fun _ => 0) := fun z =>
  ⟨hasDerivAt_const z 0, by simpa using hasDerivAt_const z (0 : ℝ)⟩

/-- Junk value outside the domain: with `D = 0` the profile equation, solved for `U''`, divides by
zero, so `IsWaveProfile 0 r c` only says `U'' = 0`; every theorem assumes `D > 0`. -/
example (r c : ℝ) : IsWaveProfile 0 r c (fun z => z) (fun _ => 1) := fun z =>
  ⟨hasDerivAt_id z, by simpa using hasDerivAt_const z (1 : ℝ)⟩

#print axioms not_eventually_pos_of_sq_lt
#print axioms isFront_azWave

end MathlibExtTest.Biology.Dynamics.FisherKPP
