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
example (t : ℝ) : ‖fmSignal 2 10 3 Real.cos t‖ = 2 :=
  norm_fmSignal 2 10 3 Real.cos (by norm_num) Real.continuous_cos t

/-- At zero amplitude the discriminator outputs `0`. -/
example (t : ℝ) : discriminatorOutput (fmSignal 0 10 3 Real.cos) t = 0 :=
  discriminatorOutput_fmSignal_zero_amplitude 10 3 Real.cos t

end PhyslibExtTest.Communications.IdealFMDiscriminator
