/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowComplete
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerMiddleShortSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerTensorInputSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerShortInputSource

/-! Unconditional source bindings for every original Ninth short and tensor coordinate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every actual middle short coordinate equals its original complete signed source cache. -/
theorem generatedNinth_actual_middle_short_input (r : GriessShortIndex) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 r =
        (generatedNinthLowerMiddleShortCoefficient r : ℝ) / 16 :=
  generatedNinth_lower_middle_short_actual generatedNinth_short_row_certificate_all r

/-- Every actual preferred short coordinate is the original normalized input coefficient. -/
theorem generatedNinth_actual_short_input (r : GriessShortIndex) :
    256 * (griessConwayEncode generatedNinthAxis).2.1 r =
      (generatedNinthLowerSpinShortInputInteger r : ℝ) :=
  generatedNinth_lower_short_input_actual generatedNinth_short_row_certificate_all r

/-- Every actual tensor coordinate is the original normalized input coefficient. -/
theorem generatedNinth_actual_tensor_input (t : SpinIndex) (i : Fin 24) :
    64 * Real.sqrt 2 * (griessConwayEncode generatedNinthAxis).2.2 t i =
      (generatedNinthLowerSpinTensorInputInteger (nortonUIntegerLabel t) i : ℝ) :=
  generatedNinth_lower_tensor_input_actual generatedNinth_short_row_certificate_all t i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
