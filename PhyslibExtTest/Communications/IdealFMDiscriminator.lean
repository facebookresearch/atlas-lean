/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Communications.IdealFMDiscriminator
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Communications.IdealFMDiscriminator

namespace PhyslibExtTest.Communications.IdealFMDiscriminator

/-- Zero message: the discriminator reads the carrier `10`. -/
example (t : ℝ) : discriminatorOutput (fmSignal 2 10 3 (fun _ => 0)) t = 10 :=
  fmDiscriminator_zero_message 2 10 3 (by norm_num) t

/-- Constant message `2` with sensitivity `3`: the discriminator
reads `10 + 3 * 2 = 16`. -/
example (t : ℝ) : discriminatorOutput (fmSignal 2 10 3 (fun _ => 2)) t = 16 := by
  have h := fmDiscriminator_const_message 2 10 3 2 (by norm_num) t
  norm_num at h
  exact h

/-- The signal has constant modulus `2`. -/
example (t : ℝ) : ‖fmSignal 2 10 3 Real.cos t‖ = 2 := by
  simpa using norm_fmSignal 2 10 3 Real.cos t

/-- At zero amplitude the discriminator outputs `0`. -/
example (t : ℝ) : discriminatorOutput (fmSignal 0 10 3 Real.cos) t = 0 :=
  discriminatorOutput_fmSignal_zero_amplitude 10 3 Real.cos t

/-- Negative nonzero amplitude: the discriminator still reads
`5 + 2 cos 1`, and the constant envelope is `|-3| = 3`. -/
example : discriminatorOutput (fmSignal (-3) 5 2 Real.cos) 1 = 5 + 2 * Real.cos 1 :=
  fmDiscriminator_cos_message (-3) 5 2 (by norm_num) 1

example : ‖fmSignal (-3) 5 2 Real.cos 1‖ = 3 := by
  rw [norm_fmSignal]; norm_num

end PhyslibExtTest.Communications.IdealFMDiscriminator
